/***************************************************************************
 *  tree_to_graphviz.h - Convert a search tree to a Graphviz graph
 *
 *  Created:   Thu 15 Apr 16:59:15 CEST 2021
 *  Copyright  2021  Till Hofmann <hofmann@kbsg.rwth-aachen.de>
 *  SPDX-License-Identifier: LGPL-3.0-or-later
 ****************************************************************************/

#pragma once

#include "search/canonical_word.h"

#include <search/search_tree.h>
#include <utilities/graphviz/graphviz.h>

#include <optional>
#include <sstream>
#include <vector>

#define VISUALIZE_DBMS false

namespace tacos::visualization {

using search::LabelReason;

/** @brief Add a search tree node to a dot graph visualization of the search tree.
 *
 * Add node as dot node to the graph. Additionally, add all its children along
 * with edges from the given node to its children.
 * @param search_node The node to add to the graph
 * @param graph The graph to add the node to
 * @param node_selector Optional node selector to select only some nodes, e.g., skip canceled nodes
 * @return The graphviz node, which can be used as reference for adding additional edges.
 */
template <typename LocationT, typename ActionT, typename ConstraintSymbolT>
std::optional<utilities::graphviz::Node>
add_search_node_to_graph(
  const search::SearchTreeNode<LocationT, ActionT, ConstraintSymbolT> *search_node,
  utilities::graphviz::Graph                                          *graph,
  std::function<bool(const search::SearchTreeNode<LocationT, ActionT, ConstraintSymbolT> &)>
    node_selector)
{
	if (!node_selector(*search_node)) {
		return std::nullopt;
	}
	std::vector<std::string> words_labels;
	std::string              program_label;
	for (const auto &word : search_node->words) {
		std::vector<std::string> word_labels;
		for (const auto &word_partition : word) {
			std::vector<std::string> partition_labels;
			for (const auto &symbol : word_partition) {
				if (std::holds_alternative<tacos::search::PlantRegionState<LocationT>>(symbol)) {
					const auto plant_location = std::get<tacos::search::PlantRegionState<LocationT>>(symbol);
					if (program_label.empty()) {
						std::stringstream s;
						s << plant_location.location;
						program_label = s.str();
					}
					partition_labels.push_back(
					  fmt::format("({}, {})", plant_location.clock, plant_location.symbolic_valuation));
				} else if(std::holds_alternative<tacos::search::PlantZoneState<LocationT>>(symbol)) {
					const auto plant_location = std::get<tacos::search::PlantZoneState<LocationT>>(symbol);
					if(program_label.empty()) {
						std::stringstream s;
						s << plant_location.location;
						program_label = s.str();
					}
					partition_labels.push_back(
						fmt::format("({}, {})", plant_location.clock, plant_location.symbolic_valuation)
					);
				} else {
					std::stringstream str;
					str << symbol;
					partition_labels.push_back(str.str());
				}
			}
			word_labels.push_back(fmt::format("{}", fmt::join(partition_labels, ", ")));
		}
		// Split the partitions into node sections (by using "|" as separator).
		// Put each word in its own group (with {}) so it is separated from the other words.
		words_labels.push_back(fmt::format("{{ {} }}", fmt::join(word_labels, " | ")));
	}

	#if VISUALIZE_DBMS
	//TODO: Trying to display the DBM takes a lot of space, and doesn't even work 100% of the time
	std::string dbm_matrix;
	{
		std::stringstream s;
		s << search_node->dbm_;
		dbm_matrix = s.str();
	}
	#endif

	std::string label_reason;
	switch (search_node->label_reason) {
	case LabelReason::UNKNOWN: label_reason = "unknown"; break;
	case LabelReason::GOOD_NODE: label_reason = "good node"; break;
	case LabelReason::BAD_NODE: label_reason = "bad node"; break;
	case LabelReason::DEAD_NODE: label_reason = "dead node"; break;
	case LabelReason::NO_ATA_SUCCESSOR: label_reason = "no ATA successor"; break;
	case LabelReason::MONOTONIC_DOMINATION: label_reason = "monotonic domination"; break;
	case LabelReason::NO_BAD_ENV_ACTION: label_reason = "no bad env action"; break;
	case LabelReason::GOOD_CONTROLLER_ACTION_FIRST:
		label_reason = "good controller action first";
		break;
	case LabelReason::BAD_ENV_ACTION_FIRST: label_reason = "bad env action first"; break;
	case LabelReason::ALL_CONTROLLER_ACTIONS_BAD: label_reason = "all ctl actions bad"; break;
	}
	#if VISUALIZE_DBMS
	const std::string node_id = fmt::format("{} | {} | {}", program_label, fmt::join(words_labels, " | "), dbm_matrix);
	const bool        new_node     = !graph->has_node(node_id);
	utilities::graphviz::Node node = graph->get_node(node_id).value_or(graph->add_node(
	  fmt::format("{} | {} | {} | {} ", label_reason, program_label, fmt::join(words_labels, " | "), dbm_matrix),
	  node_id));
	#else
	const std::string node_id = fmt::format("{} | {}", program_label, fmt::join(words_labels, " | "));
	const bool        new_node     = !graph->has_node(node_id);
	utilities::graphviz::Node node = graph->get_node(node_id).value_or(graph->add_node(
	  fmt::format("{} | {} | {}", label_reason, program_label, fmt::join(words_labels, " | ")),
	  node_id));
	#endif
	// Set the node color according to its label.
	if (search_node->label == search::NodeLabel::TOP) {
		node.set_property("color", "green");
	} else if (search_node->label == search::NodeLabel::BOTTOM) {
		node.set_property("color", "red");
	}
	if (new_node) {
		for (const auto &[action, child] : search_node->get_children()) {
			auto graphviz_child = add_search_node_to_graph(child.get(), graph, node_selector);
			if (graphviz_child) {
				graph->add_edge(node,
				                *graphviz_child,
				                fmt::format("({}, {})", action.first, action.second));
			}
		}
	}
	return node;
}

/** @brief Generate a graphviz graph visualizing the search tree.
 *
 * @param search_node The root node of the tree
 * @param node_selector Optional node selector to select only some nodes, e.g., skip canceled nodes
 * @return The search tree converted to a dot graph
 */
template <typename LocationT, typename ActionT, typename ConstraintSymbolT>
utilities::graphviz::Graph
search_tree_to_graphviz(
  const search::SearchTreeNode<LocationT, ActionT, ConstraintSymbolT> &search_node,
  std::function<bool(const search::SearchTreeNode<LocationT, ActionT, ConstraintSymbolT> &)>
    node_selector)
{
	utilities::graphviz::Graph graph;
	graph.set_property("rankdir", "LR");
	graph.set_default_node_property("shape", "record");
	add_search_node_to_graph(&search_node, &graph, node_selector);
	return graph;
}

/** @brief Generate a graphviz graph visualizing the search tree.
 *
 * @param search_node The root node of the tree
 * @param skip_canceled If true, skip nodes that have been canceled
 * @return The search tree converted to a dot graph
 */
template <typename LocationT, typename ActionT, typename ConstraintSymbolT>
utilities::graphviz::Graph
search_tree_to_graphviz(
  const search::SearchTreeNode<LocationT, ActionT, ConstraintSymbolT> &search_node,
  bool                                                                 skip_canceled = false)
{
	utilities::graphviz::Graph graph;
	graph.set_property("rankdir", "LR");
	graph.set_default_node_property("shape", "record");
	std::function<bool(const search::SearchTreeNode<LocationT, ActionT, ConstraintSymbolT> &)>
	  selector =
	    [skip_canceled](
	      const search::SearchTreeNode<LocationT, ActionT, ConstraintSymbolT> &node) -> bool {
		return !skip_canceled || node.label != search::NodeLabel::CANCELED;
	};
	add_search_node_to_graph(&search_node, &graph, selector);
	return graph;
}

} // namespace tacos::visualization
