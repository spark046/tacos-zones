/***************************************************************************
 *  test_railroad.cpp - A railroad example
 *
 *  Created:   Mon  1 Mar 17:18:27 CET 2021
 *  Copyright  2021  Till Hofmann <hofmann@kbsg.rwth-aachen.de>
 *  SPDX-License-Identifier: LGPL-3.0-or-later
 ****************************************************************************/


#define SPDLOG_ACTIVE_LEVEL SPDLOG_LEVEL_ERROR

#include "automata/automata.h"
#include "automata/ta.h"
#include "automata/ta_product.h"
#include "automata/ta_regions.h"
#include "heuristics_generator.h"
#include "mtl/MTLFormula.h"
#include "mtl_ata_translation/translator.h"
#include "railroad.h"
#include "search/canonical_word.h"
#include "search/create_controller.h"
#include "search/heuristics.h"
#include "search/search.h"
#include "search/search_tree.h"
#include "search/synchronous_product.h"
#include "search/ta_adapter.h"
#include "visualization/ta_to_graphviz.h"
#include "visualization/tree_to_graphviz.h"
#include "visualization/interactive_tree_to_graphviz.h"

#include "search/verify_ta_controller.h"

#include <fmt/format.h>
#include <fmt/ostream.h>
#include <spdlog/common.h>
#include <spdlog/spdlog.h>

#include <catch2/benchmark/catch_benchmark.hpp>
#include <catch2/catch_test_macros.hpp>
#include <catch2/generators/catch_generators.hpp>
#include <iterator>

#undef TRUE

namespace {

using namespace tacos;

using Location   = automata::ta::Location<std::string>;
using TA         = automata::ta::TimedAutomaton<std::string, std::string>;
using Transition = automata::ta::Transition<std::string, std::string>;
using F          = logic::MTLFormula<std::string>;
using AP         = logic::AtomicProposition<std::string>;
using search::NodeLabel;
using TreeSearch =
  search::RegionTreeSearch<automata::ta::Location<std::vector<std::string>>, std::string>;

TEST_CASE("Railroad", "[railroad]")
{
	const auto &[plant, spec, controller_actions, environment_actions] = create_crossing_problem({2});
	const auto   num_crossings                                         = 1;
	std::set<AP> actions;
	std::set_union(begin(controller_actions),
	               end(controller_actions),
	               begin(environment_actions),
	               end(environment_actions),
	               inserter(actions, end(actions)));
	CAPTURE(spec);
	auto ata = mtl_ata_translation::translate(spec, actions);
	CAPTURE(plant);
	CAPTURE(ata);
	const unsigned int K = std::max(plant.get_largest_constant(), spec.get_largest_constant());
	TreeSearch      search{&plant,
                    &ata,
                    controller_actions,
                    environment_actions,
                    K,
                    true,
                    true,
                    generate_heuristic<TreeSearch::Node>()};
	search.build_tree(true);
	CHECK(search.get_root()->label == NodeLabel::TOP);
	auto controller = controller_synthesis::create_controller(
						search.get_root(), controller_actions, environment_actions, 2
						);
	
	CHECK(search::verify_ta_controller(plant, controller, spec, K));
#ifdef HAVE_VISUALIZATION
	visualization::search_tree_to_graphviz(*search.get_root(), true)
	  .render_to_file(fmt::format("railroad{}.svg", num_crossings));
	visualization::ta_to_graphviz(controller_synthesis::create_controller(
	                                search.get_root(), controller_actions, environment_actions, 2),
	                              false)
	  .render_to_file(fmt::format("railroad{}_controller.pdf", num_crossings));
#endif
}

TEST_CASE("Railroad crossing benchmark", "[.benchmark][railroad]")
{
	spdlog::set_level(spdlog::level::debug);
	spdlog::set_pattern("%t %v");
	auto distances = GENERATE(
	  values({std::vector<Endpoint>{2}, std::vector<Endpoint>{2, 2}, std::vector<Endpoint>{2, 4}}));
	const auto   num_crossings       = distances.size();
	const auto   problem             = create_crossing_problem(distances);
	auto         plant               = std::get<0>(problem);
	auto         spec                = std::get<1>(problem);
	auto         controller_actions  = std::get<2>(problem);
	auto         environment_actions = std::get<3>(problem);
	std::set<AP> actions;
	std::set_union(begin(controller_actions),
	               end(controller_actions),
	               begin(environment_actions),
	               end(environment_actions),
	               inserter(actions, end(actions)));
	CAPTURE(spec);
	auto ata = mtl_ata_translation::translate(spec, actions);
	CAPTURE(plant);
	CAPTURE(ata);
	const unsigned int K = std::max(plant.get_largest_constant(), spec.get_largest_constant());

	//	auto weight_plant = GENERATE(-5, -1, 0, 1, 10);
	//	auto weight_canonical_words = GENERATE(-5, 0, 5);
	// auto weight_plant           = GENERATE(8, 10, 12, 15);
	// auto weight_canonical_words = GENERATE(4, 6, 10, 15);
	auto weight_plant           = 12;
	auto weight_canonical_words = 10;
	BENCHMARK(
	  fmt::format("Run search with weight_plant={}, weight_canonical_words={}, distances=({})",
	              weight_plant,
	              weight_canonical_words,
	              fmt::join(distances, ", ")))
	{
		TreeSearch search{&plant,
		                  &ata,
		                  controller_actions,
		                  environment_actions,
		                  K,
		                  true,
		                  true,
		                  generate_heuristic<TreeSearch::Node>(weight_canonical_words,
		                                                       weight_plant,
		                                                       environment_actions)};

		search.build_tree(true);
		CHECK(search.get_root()->label == NodeLabel::TOP);
#ifdef HAVE_VISUALIZATION
		char              tmp_filename[] = "search_graph_XXXXXX.svg";
		mkstemps(tmp_filename, 4);
		std::filesystem::path tmp_file(tmp_filename);
		visualization::search_tree_to_graphviz_interactive(search.get_root(), tmp_filename);
		visualization::ta_to_graphviz(controller_synthesis::create_controller(
		                                search.get_root(), controller_actions, environment_actions, 2),
		                              false)
		  .render_to_file(fmt::format("railroad{}_controller.pdf", num_crossings));
#endif
	};
}

} // namespace
