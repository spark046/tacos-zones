/***************************************************************************
 *  search.h - Construct the search tree over ABConfigurations
 *
 *  Created:   Mon  1 Feb 16:21:53 CET 2021
 *  Copyright  2021  Till Hofmann <hofmann@kbsg.rwth-aachen.de>
 *  SPDX-License-Identifier: LGPL-3.0-or-later
 ****************************************************************************/

#pragma once

#include "adapter.h"
#include "automata/automata.h"
#include "automata/ata.h"
#include "automata/ta.h"
#include "canonical_word.h"
#include "heuristics.h"
#include "mtl/MTLFormula.h"
#include "mtl_ata_translation/translator.h"
#include "operators.h"
#include "reg_a.h"
#include "search_tree.h"
#include "synchronous_product.h"
#include "utilities/priority_thread_pool.h"
#include "utilities/type_traits.h"
#include "utilities/types.h"

#include <fmt/ranges.h>
#include <spdlog/spdlog.h>

#include <algorithm>
#include <iterator>
#include <limits>
#include <memory>
#include <queue>
#include <variant>

/** @brief The search algorithm.
 *
 * This namespace contains the search algorithm that searches for a controller.
 */
namespace tacos::search {

/** @brief Check if the node using regions has a satisfiable ATA configuration.
 *
 * If every word in the node contains an ATA sink location, then none of those configurations is
 * satisfiable.
 * @return false if every word contains an ATA sink location
 */
template <typename Location, typename ActionType, typename ConstraintSymbolType>
bool
has_satisfiable_ata_configuration(
  const SearchTreeNode<CanonicalABWord<Location, ConstraintSymbolType>, Location, ActionType, ConstraintSymbolType> &node)
{
	return !std::all_of(std::begin(node.words), std::end(node.words), [](const auto &word) {
		return std::any_of(std::begin(word), std::end(word), [](const auto &component) {
			return std::find_if(
					std::begin(component),
					std::end(component),
					[](const auto &region_symbol) {
						return (std::holds_alternative<ATARegionState<ConstraintSymbolType>>(region_symbol)
								&& std::get<ATARegionState<ConstraintSymbolType>>(region_symbol).location
									== logic::MTLFormula<ConstraintSymbolType>{
									mtl_ata_translation::get_sink<ConstraintSymbolType>()}) ||
								(std::holds_alternative<ATAZoneState<ConstraintSymbolType>>(region_symbol)
								&& std::get<ATAZoneState<ConstraintSymbolType>>(region_symbol).location
									== logic::MTLFormula<ConstraintSymbolType>{
									mtl_ata_translation::get_sink<ConstraintSymbolType>()});
					})
				!= std::end(component);
		});
	});
}

/** @brief Check if the node has a satisfiable ATA configuration.
 *
 * If every word in the node contains an ATA sink location, then none of those configurations is
 * satisfiable.
 * @return false if every word contains an ATA sink location
 */
template <typename Location, typename ActionType, typename ConstraintSymbolType>
bool
has_satisfiable_ata_configuration(
  const SearchTreeNode<CanonicalABZoneWord<Location, ConstraintSymbolType>, Location, ActionType, ConstraintSymbolType> &node)
{
	return !std::all_of(std::begin(node.words), std::end(node.words), [](const auto &word) {
		return std::find_if(std::begin(word.ata_locations), std::end(word.ata_locations), [](const auto &location) {
			return location == 
				logic::MTLFormula<ConstraintSymbolType>{mtl_ata_translation::get_sink<ConstraintSymbolType>()};
		}) != std::end(word.ata_locations);
	});
}

namespace details {

template <typename Location, typename ActionType, typename ConstraintSymbolType, typename CanonicalWord>
void
label_graph(SearchTreeNode<CanonicalWord, Location, ActionType, ConstraintSymbolType> *node,
            const std::set<ActionType>                                 &controller_actions,
            const std::set<ActionType>                                 &environment_actions,
            std::set<SearchTreeNode<CanonicalWord, Location, ActionType, ConstraintSymbolType> *> &visited)
{
	if (node->label != NodeLabel::UNLABELED) {
		return;
	}
	if (std::find(std::begin(visited), std::end(visited), node) != std::end(visited)) {
		// This node was already visited, meaning that we have found a loop. In a loop, there is always
		// a monotonic domination, because monotonic domination is reflexive.
		node->label        = NodeLabel::TOP;
		node->label_reason = LabelReason::MONOTONIC_DOMINATION;
		return;
	}
	visited.insert(node);
	if (node->state == NodeState::GOOD) {
		node->label_reason = LabelReason::GOOD_NODE;
		node->set_label(NodeLabel::TOP);
	} else if (node->state == NodeState::DEAD) {
		node->label_reason = LabelReason::DEAD_NODE;
		node->set_label(NodeLabel::TOP);
	} else if (node->state == NodeState::BAD) {
		node->label_reason = LabelReason::BAD_NODE;
		node->set_label(NodeLabel::BOTTOM);
	} else {
		for (const auto &[action, child] : node->get_children()) {
			if (child.get() != node) {
				label_graph(child.get(), controller_actions, environment_actions, visited);
			}
		}
		bool        has_enviroment_step{false};
		RegionIndex first_good_controller_step{std::numeric_limits<RegionIndex>::max()};
		RegionIndex first_bad_environment_step{std::numeric_limits<RegionIndex>::max()};
		for (const auto &[timed_action, child] : node->get_children()) {
			const auto &[step, action] = timed_action;
			if (controller_actions.find(action) != std::end(controller_actions)) {
				assert(environment_actions.find(action) == std::end(environment_actions));
				if (child->label == NodeLabel::TOP) {
					first_good_controller_step = std::min(first_good_controller_step, step);
				}
			} else {
				assert(environment_actions.find(action) != std::end(environment_actions));
				has_enviroment_step = true;
				if (child->label != NodeLabel::TOP) {
					first_bad_environment_step = std::min(first_bad_environment_step, step);
				}
			}
		}
		// Formally, the controller selects a subset of actions U such that
		// (1) U is deterministic: it cannot select the same action twice with different clock resets)
		// (2) U is non-restricting: if there is an environment action at step i, then the controller
		// must select a controller action at step j < i or it must select the environment action (3) U
		// is non-blocking: if there is some successor, then U must not be empty. The environment then
		// selects exactly one element of U.
		if (first_good_controller_step < first_bad_environment_step) {
			// The controller can just select the good controller action.
			node->label_reason = LabelReason::GOOD_CONTROLLER_ACTION_FIRST;
			node->set_label(NodeLabel::TOP);
		} else if (has_enviroment_step
		           && first_bad_environment_step == std::numeric_limits<RegionIndex>::max()) {
			// There is an environment action and no environment action is bad
			// -> the controller can just select all environment actions
			node->label_reason = LabelReason::NO_BAD_ENV_ACTION;
			node->set_label(NodeLabel::TOP);
		} else if (!has_enviroment_step) {
			// All controller actions must be bad (otherwise we would be in the first case)
			// -> no controller strategy
			assert(first_good_controller_step == std::numeric_limits<RegionIndex>::max());
			node->label_reason = LabelReason::ALL_CONTROLLER_ACTIONS_BAD;
			node->set_label(NodeLabel::BOTTOM);
		} else {
			// There must be an environment action (otherwise case 3) and one of them must be bad
			// (otherwise case 2).
			assert(first_bad_environment_step < std::numeric_limits<RegionIndex>::max());
			node->label_reason = LabelReason::BAD_ENV_ACTION_FIRST;
			node->set_label(NodeLabel::BOTTOM);
		}
	}
}
} // namespace details

/** Label the search graph.
 *
 * Traverse the search graph and label it bottom-up.
 * @param node The node to start the traversal from, usually the root of the search graph.
 * @param controller_actions The set of actions that the controller can select.
 * @param environment_actions The set of actions that the environment can select.
 */
template <typename Location, typename ActionType, typename ConstraintSymbolType, typename CanonicalWord>
void
label_graph(SearchTreeNode<CanonicalWord, Location, ActionType, ConstraintSymbolType> *node,
            const std::set<ActionType>                                 &controller_actions,
            const std::set<ActionType>                                 &environment_actions)
{
	std::set<SearchTreeNode<CanonicalWord, Location, ActionType, ConstraintSymbolType> *> visited;
	return details::label_graph(node, controller_actions, environment_actions, visited);
}

/** @brief Search the configuration tree for a valid controller.
 *
 * This abstract class implements the main algorithm to check the existence of a controller. It builds a
 * search graph following the transitions of the plant (e.g., the TA) and the ATA and then labels
 * nodes recursively bottom-up.
 */
template <typename Location,
          typename ActionType,
          typename ConstraintSymbolType = ActionType,
          bool use_location_constraints = false,
          typename Plant =
            automata::ta::TimedAutomaton<typename Location::UnderlyingType, ActionType>,
          bool use_set_semantics = false,
		  typename Node = SearchTreeNode<CanonicalABWord<Location, ConstraintSymbolType>, Location, ActionType, ConstraintSymbolType>,
		  typename CanonicalWord = CanonicalABWord<Location, ConstraintSymbolType>>
class TreeSearch
{
public:
	/** The type of the input symbols that the ATA accepts. */
	using ATAInputType =
	  /* if use_set_semantics is true, then the ATASymbolT is the same as
	   * std::set<ConstraintSymbolType>, otherwise it is just ConstraintSymbolType> */
	  typename std::disjunction<
	    utilities::values_equal<use_set_semantics, false, ConstraintSymbolType>,
	    utilities::values_equal<use_set_semantics, true, std::set<ConstraintSymbolType>>,
	    std::void_t<void>>::type;

	/** Initialize the search.
	 * @param ta The plant to be controlled
	 * @param ata The specification of undesired behaviors
	 * @param controller_actions The actions that the controller may decide to take
	 * @param environment_actions The actions controlled by the environment
	 * @param K The maximal constant occurring in a clock constraint
	 * @param incremental_labeling True, if incremental labeling should be used (default=false)
	 * @param terminate_early If true, cancel the children of a node that has already been labeled
	 * @param search_heuristic The heuristic to use during tree expansion
	 * @param use_zones Whether to use zones, otherwise regions are used
	 */
	TreeSearch(
		// const automata::ta::TimedAutomaton<Location, ActionType> *                                ta,
		const Plant                                                                      *ta,
		automata::ata::AlternatingTimedAutomaton<logic::MTLFormula<ConstraintSymbolType>,
												 logic::AtomicProposition<ATAInputType>> *ata,
		std::set<ActionType>                   controller_actions,
		std::set<ActionType>                   environment_actions,
		RegionIndex                            K,
		bool                                   incremental_labeling = false,
		bool                                   terminate_early      = false,
		std::unique_ptr<Heuristic<long, Node>> search_heuristic =
			std::make_unique<BfsHeuristic<long, Node>>(),
		bool                                   use_zones = false)
	: ta_(ta),
	  ata_(ata),
	  controller_actions_(controller_actions),
	  environment_actions_(environment_actions),
	  K_(K),
	  incremental_labeling_(incremental_labeling),
	  terminate_early_(terminate_early),
	  use_zones_(use_zones)
	{
		static_assert(use_location_constraints || std::is_same_v<ActionType, ConstraintSymbolType>);
		// Assert that the two action sets are disjoint.
		assert(
		  std::all_of(controller_actions_.begin(), controller_actions_.end(), [this](const auto &a) {
			  return environment_actions_.find(a) == environment_actions_.end();
		  }));
		assert(
		  std::all_of(environment_actions_.begin(), environment_actions_.end(), [this](const auto &a) {
			  return controller_actions_.find(a) == controller_actions_.end();
		  }));
		
		heuristic = std::move(search_heuristic);
	}

	/** Get the root of the search tree.
	 * @return A pointer to the root, only valid as long as the TreeSearch object has not been
	 * destroyed
	 */
	Node *
	get_root() const
	{
		return tree_root_.get();
	}

	/** Check if a node is bad, i.e., if it violates the specification.
	 * @param node A pointer to the node to check
	 * @return true if the node is bad
	 */
	bool
	is_bad_node(Node *node) const
	{
		return std::any_of(node->words.begin(), node->words.end(), [this](const auto &word) {
			const auto candidate = get_candidate(word);
			return ta_->is_accepting_configuration(candidate.first)
				&& ata_->is_accepting_configuration(candidate.second);
		});
	}

	/** Add a node the processing queue. This adds a new task to the thread pool that expands the
	 * node asynchronously.
	 * @param node The node to expand */
	void
	add_node_to_queue(Node *node)
	{
		pool_.add_job([this, node] { expand_node(node); }, -heuristic->compute_cost(node));
	}

	/** Build the complete search tree by expanding nodes recursively.
	 * @param multi_threaded If set to true, run the thread pool. Otherwise, process the jobs
	 * synchronously with a single thread. */
	void
	build_tree(bool multi_threaded = true)
	{
		if (multi_threaded) {
			pool_.start();
			pool_.wait();
		} else {
			while (step()) {}
		}
	}

	/** Compute the next iteration by taking the first item of the queue and expanding it.
	 * @return true if there was still an unexpanded node
	 */
	bool
	step()
	{
		utilities::QueueAccess queue_access{&pool_};
		SPDLOG_TRACE("Getting next node from queue, queue size is {}", queue_access.get_size());
		if (queue_access.empty()) {
			return false;
		}
		auto step_function = std::get<1>(queue_access.top());
		queue_access.pop();
		step_function();
		return true;
	}

	/** Process and expand the given node.  */
	void
	expand_node(Node *node)
	{
		if (node->label != NodeLabel::UNLABELED) {
			// The node was already labeled, nothing to do.
			return;
		}
		bool is_expanding = node->is_expanding.exchange(true);
		if (is_expanding) {
			// The node is already being expanded.
			return;
		}
		SPDLOG_TRACE("Processing {}", *node);
		if (is_bad_node(node)) {
			SPDLOG_DEBUG("Node {} is BAD", *node);
			node->label_reason = LabelReason::BAD_NODE;
			node->state        = NodeState::BAD;
			node->is_expanded  = true;
			node->is_expanding = false;
			if (incremental_labeling_) {
				node->set_label(NodeLabel::BOTTOM, terminate_early_);
				node->label_propagate(controller_actions_, environment_actions_, terminate_early_);
			}
			return;
		}
		if (!has_satisfiable_ata_configuration(*node)) {
			node->label_reason = LabelReason::NO_ATA_SUCCESSOR;
			node->state        = NodeState::GOOD;
			node->is_expanded  = true;
			node->is_expanding = false;
			if (incremental_labeling_) {
				node->set_label(NodeLabel::TOP, terminate_early_);
				node->label_propagate(controller_actions_, environment_actions_, terminate_early_);
			}
			return;
		}
		if (dominates_ancestor(node)) {
			node->label_reason = LabelReason::MONOTONIC_DOMINATION;
			node->state        = NodeState::GOOD;
			node->is_expanded  = true;
			node->is_expanding = false;
			if (incremental_labeling_) {
				node->set_label(NodeLabel::TOP, terminate_early_);
				node->label_propagate(controller_actions_, environment_actions_, terminate_early_);
			}
			return;
		}

		std::set<Node *> new_children;
		std::set<Node *> existing_children;
		if (node->get_children().empty()) {
			std::tie(new_children, existing_children) = compute_children(node);
		}

		node->is_expanded  = true;
		node->is_expanding = false;
		if (node->label == NodeLabel::CANCELED) {
			// The node has been canceled in the meantime, do not add children to queue.
			return;
		}
		for (const auto &child : existing_children) {
			SPDLOG_TRACE("Found existing node for {}", fmt::ptr(child));
			if (child->label == NodeLabel::CANCELED) {
				SPDLOG_DEBUG("Expansion of {}: Found existing child {}, is canceled, re-adding",
				             fmt::ptr(node),
				             fmt::ptr(child));
				child->reset_label();
				add_node_to_queue(child);
			}
		}
		if (incremental_labeling_ && !existing_children.empty()) {
			// There is an existing child, directly check the labeling.
			SPDLOG_TRACE("Node {} has existing child, updating labels", node_to_string(*node, false));
			node->label_propagate(controller_actions_, environment_actions_, terminate_early_);
		}
		for (const auto &child : new_children) {
			add_node_to_queue(child);
		}
		SPDLOG_TRACE("Node has {} children, {} of them new",
		             node->get_children().size(),
		             new_children.size());
		if (node->get_children().empty()) {
			node->label_reason = LabelReason::DEAD_NODE;
			node->state        = NodeState::DEAD;
			if (incremental_labeling_) {
				node->set_label(NodeLabel::TOP, terminate_early_);
				node->label_propagate(controller_actions_, environment_actions_, terminate_early_);
			}
		}
	}

	/** Compute the final tree labels.
	 * @param node The node to start the labeling at (e.g., the root of the tree)
	 */
	void
	label(Node *node = nullptr)
	{
		if (node == nullptr) {
			node = get_root();
		}
		return label_graph(node, controller_actions_, environment_actions_);
	}

	/** Get the size of the search graph.
	 * @return The number of nodes in the search graph
	 */
	size_t
	get_size() const
	{
		std::lock_guard lock{nodes_mutex_};
		return nodes_.size();
	}

	/** Get the current search nodes. */
	const std::map<std::set<CanonicalWord>, std::shared_ptr<Node>> &
	get_nodes()
	{
		return nodes_;
	}

	protected:

	virtual
	std::pair<std::set<Node *>, std::set<Node *>>
	compute_children(Node *node) = 0;

	std::pair<std::set<Node *>, std::set<Node *>>
	insert_children(std::map<std::pair<RegionIndex, ActionType>, std::set<CanonicalWord>> child_classes, Node *node)
	{
		std::set<Node *> new_children;
		std::set<Node *> existing_children;
		// Create child nodes, where each child contains all successors words of
		// the same reg_a class.
		{
			std::lock_guard lock{nodes_mutex_};
			for (const auto &[timed_action, words] : child_classes) {
				auto [child_it, is_new] = nodes_.insert({words, std::make_shared<Node>(words)});
				const std::shared_ptr<Node> &child_ptr = child_it->second;
				node->add_child(timed_action, child_ptr);
				SPDLOG_TRACE("Action ({}, {}): Adding child {}",
							timed_action.first,
							timed_action.second,
							words);
				if (is_new) {
					new_children.insert(child_ptr.get());
				} else {
					existing_children.insert(child_ptr.get());
				}
			}
		}
		return {new_children, existing_children};
	}

protected:

	const Plant *const ta_;
	const automata::ata::AlternatingTimedAutomaton<logic::MTLFormula<ConstraintSymbolType>,
												   logic::AtomicProposition<ATAInputType>>
		*const ata_;

	const std::set<ActionType> controller_actions_;
	const std::set<ActionType> environment_actions_;
	RegionIndex                K_;
	const bool                 incremental_labeling_;
	const bool                 terminate_early_{false};
	const bool                 use_zones_;

	mutable std::mutex    nodes_mutex_;
	std::shared_ptr<Node> tree_root_;
	std::map<std::set<CanonicalWord>, std::shared_ptr<Node>> nodes_;
	utilities::ThreadPool<long> pool_{utilities::ThreadPool<long>::StartOnInit::NO};
	std::unique_ptr<Heuristic<long, SearchTreeNode<CanonicalWord, Location, ActionType, ConstraintSymbolType>>>
	  heuristic;
};

/**
 * This is the class for search trees using regions.
 */
template <typename Location,
          typename ActionType,
          typename ConstraintSymbolType = ActionType,
          bool use_location_constraints = false,
          typename Plant =
            automata::ta::TimedAutomaton<typename Location::UnderlyingType, ActionType>,
          bool use_set_semantics = false>
class RegionTreeSearch : public TreeSearch<Location, ActionType, ConstraintSymbolType, use_location_constraints, Plant, use_set_semantics,
									SearchTreeNode<CanonicalABWord<Location, ConstraintSymbolType>, Location, ActionType, ConstraintSymbolType>,
									CanonicalABWord<Location, ConstraintSymbolType>>
{
	//C++ compilers are dumb dumbs and you cannot properly inherit from templated Base Classes
	using Base = TreeSearch<Location, ActionType, ConstraintSymbolType, use_location_constraints, Plant, use_set_semantics,
					SearchTreeNode<CanonicalABWord<Location, ConstraintSymbolType>, Location, ActionType, ConstraintSymbolType>,
					CanonicalABWord<Location, ConstraintSymbolType>>;
	using Base::ta_;
	using Base::ata_;
	using Base::controller_actions_;
	using Base::environment_actions_;
	using Base::K_;
	using Base::tree_root_;
	using Base::nodes_;

	using Base::add_node_to_queue;
	using Base::insert_children;

	public:
	using Node = SearchTreeNode<CanonicalABWord<Location, ConstraintSymbolType>, Location, ActionType, ConstraintSymbolType>;
	/** The type of the input symbols that the ATA accepts. */
	using ATAInputType =
	  /* if use_set_semantics is true, then the ATASymbolT is the same as
	   * std::set<ConstraintSymbolType>, otherwise it is just ConstraintSymbolType> */
	  typename std::disjunction<
	    utilities::values_equal<use_set_semantics, false, ConstraintSymbolType>,
	    utilities::values_equal<use_set_semantics, true, std::set<ConstraintSymbolType>>,
	    std::void_t<void>>::type;

	/** Initialize the search tree using regions.
	 * 
	 * TODO: Allow for Heuristics as a parameter (doesn't work currently due to unique pointer)
	 * @param ta The plant to be controlled
	 * @param ata The specification of undesired behaviors
	 * @param controller_actions The actions that the controller may decide to take
	 * @param environment_actions The actions controlled by the environment
	 * @param K The maximal constant occurring in a clock constraint
	 * @param incremental_labeling True, if incremental labeling should be used (default=false)
	 * @param terminate_early If true, cancel the children of a node that has already been labeled
	 * @param search_heuristic The heuristic to use during tree expansion
	 * @param use_zones Whether to use zones, otherwise regions are used
	 */
	RegionTreeSearch(
		const Plant                           *ta,
		automata::ata::AlternatingTimedAutomaton<logic::MTLFormula<ConstraintSymbolType>,
												 logic::AtomicProposition<ATAInputType>> *ata,
		std::set<ActionType>                   controller_actions,
		std::set<ActionType>                   environment_actions,
		RegionIndex                            K,
		bool                                   incremental_labeling = false,
		bool                                   terminate_early      = false)
	: Base(ta, ata, controller_actions, environment_actions, K, incremental_labeling, terminate_early)
	{
		if constexpr (use_location_constraints && use_set_semantics) {
			// Already read a single empty symbol to skip l0.
			const auto ata_configurations =
			  ata->make_symbol_step(ata->get_initial_configuration(),
			                        logic::AtomicProposition<ATAInputType>{{}});
			std::set<CanonicalABWord<typename Plant::Location, ConstraintSymbolType>> initial_words;
			for (const auto &ata_configuration : ata_configurations) {
				initial_words.insert(
				  get_canonical_word(ta->get_initial_configuration(), ata_configuration, K));
			}

			tree_root_ = std::make_shared<Node>(initial_words);
		} else {
			tree_root_ = std::make_shared<Node>(
			  std::set<CanonicalABWord<typename Plant::Location, ConstraintSymbolType>>{
			    get_canonical_word(ta->get_initial_configuration(),
			                       ata->get_initial_configuration(),
			                       K)});
		}
		nodes_                                  = {{{}, tree_root_}};
		tree_root_->min_total_region_increments = 0;
		add_node_to_queue(tree_root_.get());
	}

	std::pair<std::set<Node *>, std::set<Node *>>
	compute_children(Node *node)
	{
		if (node == nullptr) {
			return {};
		}
		assert(node->get_children().empty());
		std::map<std::pair<RegionIndex, ActionType>,
				 std::set<CanonicalABWord<Location, ConstraintSymbolType>>>
			child_classes;

		const auto time_successors = get_time_successors(node->words, K_);
		for (std::size_t increment = 0; increment < time_successors.size(); ++increment) {
			for (const auto &time_successor : time_successors[increment]) {
				std::multimap<ActionType, CanonicalABWord<Location, ConstraintSymbolType>> successors =
				get_next_canonical_words<Plant,
										ActionType,
										ConstraintSymbolType,
										use_location_constraints,
										use_set_semantics>(controller_actions_, environment_actions_)(
								*ta_, *ata_, get_candidate(time_successor), increment, K_, false);

				for (const auto &[symbol, successor] : successors) {
					assert(
					std::find(std::begin(controller_actions_), std::end(controller_actions_), symbol)
						!= std::end(controller_actions_)
					|| std::find(std::begin(environment_actions_), std::end(environment_actions_), symbol)
						!= std::end(environment_actions_));
					child_classes[std::make_pair(increment, symbol)].insert(successor);
				}
			}
		}

		return insert_children(child_classes, node);
	}
};

/**
 * This is the class for search trees using zones.
 */
template <typename Location,
          typename ActionType,
          typename ConstraintSymbolType = ActionType,
          bool use_location_constraints = false,
          typename Plant =
            automata::ta::TimedAutomaton<typename Location::UnderlyingType, ActionType>,
          bool use_set_semantics = false>
class ZoneTreeSearch : public TreeSearch<Location, ActionType, ConstraintSymbolType, use_location_constraints, Plant, use_set_semantics,
								  SearchTreeNode<CanonicalABZoneWord<Location, ConstraintSymbolType>, Location, ActionType, ConstraintSymbolType>,
								  CanonicalABZoneWord<Location, ConstraintSymbolType>>
{
	//C++ compilers are dumb dumbs and you cannot properly inherit from templated Base Classes
	using Base = TreeSearch<Location, ActionType, ConstraintSymbolType, use_location_constraints, Plant, use_set_semantics,
					SearchTreeNode<CanonicalABZoneWord<Location, ConstraintSymbolType>, Location, ActionType, ConstraintSymbolType>,
					CanonicalABZoneWord<Location, ConstraintSymbolType>>;
	using Base::ta_;
	using Base::ata_;
	using Base::controller_actions_;
	using Base::environment_actions_;
	using Base::K_;
	using Base::tree_root_;
	using Base::nodes_;

	using Base::add_node_to_queue;
	using Base::insert_children;

	public:
	using Node = SearchTreeNode<CanonicalABZoneWord<Location, ConstraintSymbolType>, Location, ActionType, ConstraintSymbolType>;
	/** The type of the input symbols that the ATA accepts. */
	using ATAInputType =
	  /* if use_set_semantics is true, then the ATASymbolT is the same as
	   * std::set<ConstraintSymbolType>, otherwise it is just ConstraintSymbolType> */
	  typename std::disjunction<
	    utilities::values_equal<use_set_semantics, false, ConstraintSymbolType>,
	    utilities::values_equal<use_set_semantics, true, std::set<ConstraintSymbolType>>,
	    std::void_t<void>>::type;

	/** Initialize the search tree using regions.
	 * 
	 * TODO: Allow for Heuristics as a parameter (doesn't work currently due to unique pointer)
	 * @param ta The plant to be controlled
	 * @param ata The specification of undesired behaviors
	 * @param controller_actions The actions that the controller may decide to take
	 * @param environment_actions The actions controlled by the environment
	 * @param K The maximal constant occurring in a clock constraint
	 * @param incremental_labeling True, if incremental labeling should be used (default=false)
	 * @param terminate_early If true, cancel the children of a node that has already been labeled
	 * @param search_heuristic The heuristic to use during tree expansion
	 * @param use_zones Whether to use zones, otherwise regions are used
	 */
	ZoneTreeSearch(
		const Plant                           *ta,
		automata::ata::AlternatingTimedAutomaton<logic::MTLFormula<ConstraintSymbolType>,
												 logic::AtomicProposition<ATAInputType>> *ata,
		std::set<ActionType>                   controller_actions,
		std::set<ActionType>                   environment_actions,
		RegionIndex                            K,
		bool                                   incremental_labeling = false,
		bool                                   terminate_early      = false)
	: Base(ta, ata, controller_actions, environment_actions, K, incremental_labeling, terminate_early)
	{
		if constexpr (use_location_constraints && use_set_semantics) {
			//TODO: Add zone support for location constraints and set semantics
		} else {
			std::multimap<std::string, automata::ClockConstraint> clock_constraints;

			for(auto clock = ta->get_clocks().begin(); clock != ta->get_clocks().end(); clock++) {
				clock_constraints.insert({*clock, automata::AtomicClockConstraintT<std::equal_to<Time>>(0)});
			}
			clock_constraints.insert({"l0", automata::AtomicClockConstraintT<std::equal_to<Time>>(0)});

			tree_root_ = std::make_shared<Node>(
			  std::set<CanonicalABZoneWord<typename Plant::Location, ConstraintSymbolType>>{
			    CanonicalABZoneWord(ta->get_initial_configuration(),
			                        ata->get_initial_configuration(),
			                        K)});
		}
		nodes_                                  = {{{}, tree_root_}};
		tree_root_->min_total_region_increments = 0;
		add_node_to_queue(tree_root_.get());
	}

	//private:
	//public for testing
	std::map<std::pair<RegionIndex, ActionType>, std::set<CanonicalABZoneWord<Location, ConstraintSymbolType>>>
	compute_next_canonical_words(const CanonicalABZoneWord<Location, ConstraintSymbolType> &word)
	{
		using ATAConfiguration = automata::ata::ZoneConfiguration<logic::MTLFormula<ConstraintSymbolType>>;
		using CanonicalABZoneWord = CanonicalABZoneWord<Location, ConstraintSymbolType>;
		//TODO I think for Golog plants the weird thing for adapters is still necessary, so add a zone adapter or something
		//TODO Also location constraints aren't added

		//Make sure the zones are consistent, and also the TA's clocks should be the same as the word's clocks
		assert(word.is_valid());
		assert(ta_->get_clocks() == word.ta_clocks);

		//Take every symbol transition from TA and ATA in order to intersect the current zone with the transition guards.

		//Successors of this canonical word, together with the needed action and time increment in order to reach it
		std::map<std::pair<RegionIndex, ActionType>, std::set<CanonicalABZoneWord>> successors;

		//Compute all successors once without delay, and then once with delays
		for(bool delay : {false, true}) {
			for(const auto &symbol : ta_->get_alphabet()) {
				Location location = word.ta_location;

				//new DBM for the TA part
				zones::Zone_DBM ta_dbm = word.dbm;

				if(delay) {
					ta_dbm.delay();
				}

				//CanonicalABZoneWord containing only the TA part
				CanonicalABZoneWord ta_word;

				//TA-Transition
				auto [curr_transition, last_transition] = ta_->get_transitions().equal_range(location);
				for(; curr_transition != last_transition; curr_transition++) {
					//0. Check whether this transition is for the current symbol
					if(curr_transition->second.symbol_ != symbol) {
						continue;
					}

					//1. Intersect the constraints of transition with the zone
					auto clock_constraints = curr_transition->second.get_guards();
					ta_dbm.conjunct(clock_constraints);

					//1.5 if a DBM became inconsistent, ignore this transition
					if(!ta_dbm.is_consistent()) {
						continue;
					}

					//2. Reset Zones
					for (const auto &clock : curr_transition->second.clock_resets_) {
						ta_dbm.reset(clock);
					}

					ta_dbm.normalize();

					//3. Calculate new Location and set the TA successor
					ta_word = CanonicalABZoneWord{curr_transition->second.target_, word.ta_clocks, {}, ta_dbm.get_subset(ta_->get_clocks())};
				}

				//The TA-Clocks will be empty if there was no valid transition
				//So we go to next symbol
				if(ta_word.ta_clocks.empty()) {
					continue;
				}

				//ATA Transitions
				//Set of new words, where the ATA would be different
				std::set<CanonicalABZoneWord> new_words;

				//Starting Configuration
				std::set<logic::MTLFormula<ConstraintSymbolType>> start_locations = word.ata_locations;
				
				// A vector of a set of target configurations that are reached when following a transition.
				// One entry for each start state
				std::vector<std::set<ATAConfiguration>> models;

				if (start_locations.empty()) {
					models = {{{}}};
				}


				for(const auto &start_location : start_locations) {
					//New DBM used only to interserct the zone to get minimal models
					zones::Zone_DBM new_dbm = ta_dbm;

					if(delay) {
						new_dbm.delay();
					}

					//Get a valid transition
					//TODO implement location constraints
					if constexpr (!use_location_constraints) {
						auto t = std::find_if(ata_->get_transitions().cbegin(), ata_->get_transitions().cend(), [&](const auto &t) {
							return t.source_ == start_location && t.symbol_ == logic::AtomicProposition{symbol};
						});
						if (t == ata_->get_transitions().end()) {
							continue;
						}

						//1. Intersect Zone for the minimal model
						auto clock_constraints = t->get_clock_constraints();
						for(const auto &constraint : clock_constraints) {
							new_dbm.conjunct(ata_formula_to_string(start_location), constraint);
						}

						//Minimal Models for this state and transition
						std::set<ATAConfiguration> new_configurations = t->get_minimal_models(new_dbm.get_zone_slice(ata_formula_to_string(start_location)));

						models.push_back(new_configurations);
					}
				}

				//The model is empty, i.e. no meaningful transition could be made
				bool model_is_empty = false;
				if(models.empty() || std::any_of(std::begin(models), std::end(models), [](const auto &model) {
					return model.empty();
				})) {
					//copy ta_word
					CanonicalABZoneWord ata_word = ta_word;

					//Check whether we have sink location or not
					if(ata_->get_sink_location().has_value()) {
						//Insert sink as ATA location
						ata_word.add_ata_location(ata_->get_sink_location().value());
						new_words.insert(ata_word);
					} else {
						//ATA part is empty
						new_words.insert(ata_word);
					}
					model_is_empty = true;
				}

				if(!model_is_empty) {
					//Following Logic from ata.hpp
					//Basically split up all minimal models from first state so each entry in each state is its minimal model.

					ranges::for_each(models[0],
						[&](const auto &state_model) {
							CanonicalABZoneWord ata_word = ta_word;
							for(const auto &raw_state : state_model) {
								//Check whether zone was reset
								if(raw_state.zone.lower_bound_ == 0 && raw_state.zone.upper_bound_ == 0 &&
								  !raw_state.zone.lower_isOpen_ && !raw_state.zone.upper_isOpen_)
								{
									ata_word.add_ata_location(raw_state.location, true);
								} else {
									ata_word.add_ata_location(raw_state.location, false);
									std::vector<automata::ClockConstraint> new_constraints = zones::get_clock_constraints_from_zone(raw_state.zone, K_);
									for(const auto &constraint : new_constraints) {
										ata_word.dbm.conjunct(ata_formula_to_string(raw_state.location), constraint);
									}
								}
							}
							new_words.insert(ata_word);
						});

					// Add models from the other configurations
					std::for_each(std::next(models.begin()), models.end(), [&](const auto &state_models) {
						std::set<CanonicalABZoneWord> expanded_words;
						ranges::for_each(state_models, [&](const auto &state_model) {
							ranges::for_each(new_words, [&](const auto &ata_word) {
								auto expanded_word = ata_word;
								for(const auto &raw_state : state_model) {
									//Check whether zone was reset
									if(raw_state.zone.lower_bound_ == 0 && raw_state.zone.upper_bound_ == 0 &&
									!raw_state.zone.lower_isOpen_ && !raw_state.zone.upper_isOpen_)
									{
										expanded_word.add_ata_location(raw_state.location, true);
									} else {
										expanded_word.add_ata_location(raw_state.location, false);
										std::vector<automata::ClockConstraint> new_constraints = zones::get_clock_constraints_from_zone(raw_state.zone, K_);
										for(const auto &constraint : new_constraints) {
											expanded_word.dbm.conjunct(ata_formula_to_string(raw_state.location), constraint);
										}
									}
								}
								expanded_words.insert(expanded_word);
							});
						});
						new_words = expanded_words;
					});
					assert(!new_words.empty());
				}

				//Insert new CanonicalABZoneWords to successors
				
				for(const auto &new_word : new_words) {
					//Calculate increment
					RegionIndex increment = 0;
					if(delay) {
						increment = word.dbm.get_increment(new_word.dbm);
						//increment must be at least one if there was a delay
						if(increment < 1) {
							increment = 1;
						}
					}
					successors[std::make_pair(increment, symbol)].insert( new_word );
				}
			}
		}

		return successors;
	}

	private:
	std::pair<std::set<Node *>, std::set<Node *>>
	compute_children(Node *node)
	{
		if (node == nullptr) {
			return {};
		}
		assert(node->get_children().empty());
		std::map<std::pair<RegionIndex, ActionType>,
				 std::set<CanonicalABZoneWord<Location, ConstraintSymbolType>>>
			child_classes;

		for(const auto &word : node->words) {
			std::map<std::pair<RegionIndex, ActionType>,
						std::set<CanonicalABZoneWord<Location, ConstraintSymbolType>>>
				successors = compute_next_canonical_words(word);

			//If this action and increment hasn't been taken yet, just insert it normally
			//Otherwise insert the new canonical words into the set that is found at this key
			for(const auto &[key, set] : successors) {
				if(!child_classes.insert({key, set}).second) {
					child_classes.at(key).insert(set.begin(), set.end());
				}
			}
		}

		return insert_children(child_classes, node);
	}
};

} // namespace tacos::search
