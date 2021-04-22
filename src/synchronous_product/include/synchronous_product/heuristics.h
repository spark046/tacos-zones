/***************************************************************************
 *  heuristics.h - Heuristics to evaluate search tree nodes
 *
 *  Created:   Tue 23 Mar 09:05:55 CET 2021
 *  Copyright  2021  Till Hofmann <hofmann@kbsg.rwth-aachen.de>
 ****************************************************************************/
/*  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation; either version 2 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU Library General Public License for more details.
 *
 *  Read the full text in the LICENSE.md file.
 */

#ifndef SRC_SYNCHRONOUS_PRODUCT_INCLUDE_SYNCHRONOUS_PRODUCT_HEURISTICS_H
#define SRC_SYNCHRONOUS_PRODUCT_INCLUDE_SYNCHRONOUS_PRODUCT_HEURISTICS_H

#include "search_tree.h"

#include <limits>

namespace synchronous_product {

/** The heuristics interface.
 * @tparam ValueT The value type of the heuristic function
 * @tparam LocationT The type of the location of an automaton
 * @tparam ActionT The type of an action of an automaton
 */
template <typename ValueT, typename LocationT, typename ActionT>
class Heuristic
{
public:
	/** @brief Compute the cost of the given node.
	 * The higher the cost, the lower the priority.
	 * @param node The node to compute the cost for
	 * @return The cost of the node
	 */
	virtual ValueT compute_cost(SearchTreeNode<LocationT, ActionT> *node) = 0;
	/** Virtual destructor. */
	virtual ~Heuristic()
	{
	}
};

/** @brief The BFS heuristic.
 * The BFS heuristic simply increases the cost with every evaluated node and therefore
 * processes them just like a FIFO queue, resulting in breadth-first sarch.
 * @tparam ValueT The value type of the heuristic function
 * @tparam LocationT The type of the location of an automaton
 * @tparam ActionT The type of an action of an automaton
 */
template <typename ValueT, typename LocationT, typename ActionT>
class BfsHeuristic : public Heuristic<ValueT, LocationT, ActionT>
{
public:
	/** @brief Compute the cost of the given node.
	 * The cost will strictly monotonically increase for each node, thereby emulating breadth-first
	 * search.
	 * @return The cost of the node
	 */
	ValueT
	compute_cost(SearchTreeNode<LocationT, ActionT> *) override
	{
		return ++node_counter;
	}

private:
	std::atomic_size_t node_counter{0};
};

/** @brief The DFS heuristic.
 * The BFS heuristic simply decreases the cost with every evaluated node and therefore
 * processes them just like a LIFO queue, resulting in depth-first sarch.
 */
template <typename ValueT, typename LocationT, typename ActionT>
class DfsHeuristic : public Heuristic<ValueT, LocationT, ActionT>
{
public:
	/** @brief Compute the cost of the given node.
	 * The cost will strictly monotonically increase for each node, thereby emulating breadth-first
	 * search.
	 * @return The cost of the node
	 */
	ValueT
	compute_cost(SearchTreeNode<LocationT, ActionT> *) override
	{
		return -(++node_counter);
	}

private:
	std::atomic_size_t node_counter{0};
};

/** @brief The Time heuristic, which prefers early actions.
 * This heuristic computes the accumulated time from the root node to the current node and
 * prioritizes nodes that occur early.
 * */
template <typename ValueT, typename LocationT, typename ActionT>
class TimeHeuristic : public Heuristic<ValueT, LocationT, ActionT>
{
public:
	/** @brief Compute the cost of the given node.
	 * The cost will strictly monotonically increase for each node, thereby emulating breadth-first
	 * search.
	 * @param node The node to compute the cost for
	 * @return The cost of the node
	 */
	ValueT
	compute_cost(SearchTreeNode<LocationT, ActionT> *node) override
	{
		ValueT cost = 0;
		for (auto current_node = node; current_node->parent != nullptr;
		     current_node      = current_node->parent) {
			ValueT node_cost = std::numeric_limits<ValueT>::max();
			for (const auto &action : current_node->incoming_actions) {
				node_cost = std::min(node_cost, ValueT{action.first});
			}
			cost += node_cost;
		}
		return cost;
	}
};

} // namespace synchronous_product

#endif /* ifndef SRC_SYNCHRONOUS_PRODUCT_INCLUDE_SYNCHRONOUS_PRODUCT_HEURISTICS_H */
