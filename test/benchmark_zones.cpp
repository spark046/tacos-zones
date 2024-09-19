/***************************************************************************
 *  benchmark_robot.cpp - Control a robot's camera
 *
 *  Created:   Mon 26 Jul 18:48:06 CEST 2021
 *  Copyright  2021  Till Hofmann <hofmann@kbsg.rwth-aachen.de>
 *  SPDX-License-Identifier: LGPL-3.0-or-later
 ****************************************************************************/

#include "automata/automata.h"
#include "automata/ta_product.h"
#include "heuristics_generator.h"
#include "mtl/MTLFormula.h"
#include "mtl_ata_translation/translator.h"
#include "search/create_controller.h"
#include "search/heuristics.h"
#include "search/search.h"
#include "search/ta_adapter.h"
#include "search/verify_ta_controller.h"

#include "automata/ta.h"
#include "automata/ta_regions.h"
#include "railroad.h"
#include "search/canonical_word.h"
#include "search/search_tree.h"
#include "search/synchronous_product.h"

#include <benchmark/benchmark.h>
#include <fmt/format.h>
#include <fmt/ostream.h>
#include <spdlog/common.h>
#include <spdlog/spdlog.h>

#include <stdexcept>

enum class Mode {
	SIMPLE,
	WEIGHTED,
	SCALED,
};

using namespace tacos;

using Search = search::ZoneTreeSearch<automata::ta::Location<std::vector<std::string>>, std::string>;
using TA     = automata::ta::TimedAutomaton<std::string, std::string>;
using MTLFormula = logic::MTLFormula<std::string>;
using AP         = logic::AtomicProposition<std::string>;
using automata::AtomicClockConstraintT;

using Location   = automata::ta::Location<std::string>;
using TA         = automata::ta::TimedAutomaton<std::string, std::string>;
using Transition = automata::ta::Transition<std::string, std::string>;
using F          = logic::MTLFormula<std::string>;
using TreeSearch = search::ZoneTreeSearch<automata::ta::Location<std::vector<std::string>>, std::string>;

using CBTreeSearch = search::ZoneTreeSearch<automata::ta::Location<std::string>, std::string>;

static void
BM_Robot_zone(benchmark::State &state, bool weighted = true, bool multi_threaded = true)
{
	spdlog::set_level(spdlog::level::err);
	spdlog::set_pattern("%t %v");
	const std::set<std::string> robot_actions = {"move", "arrive", "pick", "put"};
	TA                          robot(
    {
      TA::Location{"AT-OUTPUT"},
      TA::Location{"PICKED"},
      TA::Location{"AT-DELIVERY"},
      TA::Location{"PUT"},
      TA::Location{"MOVING-TO-OUTPUT"},
      TA::Location{"MOVING-TO-DELIVERY"},
    },
    robot_actions,
    TA::Location{"MOVING-TO-OUTPUT"},
    {TA::Location{"AT-OUTPUT"}},
    {"c-travel", "cp"},
    {
      TA::Transition(TA::Location{"PICKED"}, "move", TA::Location{"MOVING-TO-DELIVERY"}),
      TA::Transition(TA::Location{"PUT"}, "move", TA::Location{"MOVING-TO-OUTPUT"}),
      TA::Transition(TA::Location{"MOVING-TO-DELIVERY"},
                     "arrive",
                     TA::Location{"AT-DELIVERY"},
                     {{"c-travel", AtomicClockConstraintT<std::equal_to<Time>>{3}}},
                     {"c-travel", "cp"}),
      TA::Transition(TA::Location{"MOVING-TO-OUTPUT"},
                     "arrive",
                     TA::Location{"AT-OUTPUT"},
                     {{"c-travel", AtomicClockConstraintT<std::equal_to<Time>>{3}}},
                     {"c-travel", "cp"}),
      TA::Transition(TA::Location{"AT-OUTPUT"},
                     "pick",
                     TA::Location{"PICKED"},
                     {{"cp", AtomicClockConstraintT<std::equal_to<Time>>{1}}}),
      TA::Transition(TA::Location{"AT-DELIVERY"},
                     "put",
                     TA::Location{"PUT"},
                     {{"cp", AtomicClockConstraintT<std::equal_to<Time>>{1}}}),
    });

	const std::set<std::string> camera_actions = {"switch-on", "switch-off"};
	TA                          camera({TA::Location{"CAMERA-OFF"}, TA::Location{"CAMERA-ON"}},
            camera_actions,
            TA::Location{"CAMERA-OFF"},
            {TA::Location{"CAMERA-OFF"}},
            {"c-camera"},
            {TA::Transition(TA::Location{"CAMERA-OFF"},
                            "switch-on",
                            TA::Location{"CAMERA-ON"},
                            {{"c-camera", AtomicClockConstraintT<std::greater_equal<Time>>{1}}},
                            {"c-camera"}),
             TA::Transition(TA::Location{"CAMERA-ON"},
                            "switch-off",
                            TA::Location{"CAMERA-OFF"},
                            {{"c-camera", AtomicClockConstraintT<std::greater_equal<Time>>{1}},
                             {"c-camera", AtomicClockConstraintT<std::less_equal<Time>>{4}}},
                            {"c-camera"})});
	const auto       product = automata::ta::get_product<std::string, std::string>({robot, camera});
	const MTLFormula pick{AP{"pick"}};
	const MTLFormula put{AP{"put"}};
	const MTLFormula camera_on{AP{"switch-on"}};
	const MTLFormula camera_off{AP{"switch-off"}};
	const auto spec = (!camera_on).until(pick) || finally(camera_off && (!camera_on).until(pick))
	                  || finally(camera_on && finally(pick, logic::TimeInterval(0, 1)))
	                  || (!camera_on).until(put) || finally(camera_off && (!camera_on).until(put))
	                  || finally(camera_on && finally(put, logic::TimeInterval(0, 1)));
	std::set<AP> action_aps;
	for (const auto &a : robot_actions) {
		action_aps.emplace(a);
	}
	for (const auto &a : camera_actions) {
		action_aps.emplace(a);
	}
	auto               ata = mtl_ata_translation::translate(spec, action_aps);
	const unsigned int K   = std::max(product.get_largest_constant(), spec.get_largest_constant());

	std::size_t tree_size        = 0;
	std::size_t pruned_tree_size = 0;
	std::size_t controller_size  = 0;
	std::size_t plant_size       = 0;

	std::unique_ptr<search::Heuristic<long, Search::Node>> heuristic;

	for (auto _ : state) {
		if (weighted) {
			heuristic = generate_heuristic<Search::Node>(state.range(0),
			                                             state.range(1),
			                                             robot_actions,
			                                             state.range(2));
		} else {
			if (state.range(0) == 0) {
				heuristic = std::make_unique<search::BfsHeuristic<long, Search::Node>>();
			} else if (state.range(0) == 1) {
				heuristic = std::make_unique<search::DfsHeuristic<long, Search::Node>>();
			} else if (state.range(0) == 2) {
				heuristic = std::make_unique<search::NumCanonicalWordsHeuristic<long, Search::Node>>();
			} else if (state.range(0) == 3) {
				heuristic = std::make_unique<
				  search::PreferEnvironmentActionHeuristic<long, Search::Node, std::string>>(robot_actions);
			} else if (state.range(0) == 4) {
				heuristic = std::make_unique<search::TimeHeuristic<long, Search::Node>>();
			} else if (state.range(0) == 5) {
				heuristic = std::make_unique<search::RandomHeuristic<long, Search::Node>>(time(NULL));
			} else {
				throw std::invalid_argument("Unexpected argument");
			}
		}
		Search search(
		  &product, &ata, camera_actions, robot_actions, K, true, true, std::move(heuristic));
		search.build_tree(multi_threaded);
		search.label();
		tree_size += search.get_size();
		std::for_each(std::begin(search.get_nodes()),
		              std::end(search.get_nodes()),
		              [&pruned_tree_size](const auto &node) {
			              if (node.second->label != search::NodeLabel::CANCELED
			                  && node.second->label != search::NodeLabel::UNLABELED) {
				              pruned_tree_size += 1;
			              }
		              });
		plant_size += product.get_locations().size();
		auto controller =
		  controller_synthesis::create_controller(search.get_root(), camera_actions, robot_actions, K);

		assert(tacos::search::verify_ta_controller(product, controller, spec, K));
		controller_size += controller.get_locations().size();
	}
	state.counters["tree_size"] =
	  benchmark::Counter(static_cast<double>(tree_size), benchmark::Counter::kAvgIterations);
	state.counters["pruned_tree_size"] =
	  benchmark::Counter(static_cast<double>(pruned_tree_size), benchmark::Counter::kAvgIterations);
	state.counters["controller_size"] =
	  benchmark::Counter(static_cast<double>(controller_size), benchmark::Counter::kAvgIterations);
	state.counters["plant_size"] =
	  benchmark::Counter(static_cast<double>(plant_size), benchmark::Counter::kAvgIterations);
}

BENCHMARK_CAPTURE(BM_Robot_zone, single_heuristic, false)
  ->DenseRange(0, 5, 1)
  ->MeasureProcessCPUTime()
  ->Unit(benchmark::kSecond)
  ->UseRealTime();
BENCHMARK_CAPTURE(BM_Robot_zone, single_heuristic_single_thread, false, false)
  ->DenseRange(0, 5, 1)
  ->MeasureProcessCPUTime()
  ->Unit(benchmark::kSecond)
  ->UseRealTime();
// Single-threaded with weighted heuristics.
BENCHMARK_CAPTURE(BM_Robot_zone, weighted_single_thread, true, false)
  ->Args({16, 4, 1})
  ->MeasureProcessCPUTime()
  ->Unit(benchmark::kSecond)
  ->UseRealTime();

BENCHMARK_CAPTURE(BM_Robot_zone, weighted, true)
  ->ArgsProduct({benchmark::CreateRange(1, 16, 2),
                 benchmark::CreateRange(1, 16, 2),
                 benchmark::CreateDenseRange(0, 2, 1)})
  ->MeasureProcessCPUTime()
  ->Unit(benchmark::kSecond)
  ->UseRealTime();

//~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~RAILROAD~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

static void
BM_Railroad_zone(benchmark::State &state, Mode mode, bool multi_threaded = true)
{
	spdlog::set_level(spdlog::level::err);
	spdlog::set_pattern("%t %v");
	std::vector<Endpoint> distances;
	switch (mode) {
	case Mode::SIMPLE:
	case Mode::WEIGHTED: distances = {2, 2}; break;
	case Mode::SCALED:
		for (std::size_t i = 0; i < 3; ++i) {
			if (state.range(i) > 0) {
				distances.push_back(state.range(i));
			}
		}
		break;
	}
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
	auto               ata = mtl_ata_translation::translate(spec, actions);
	const unsigned int K   = std::max(plant.get_largest_constant(), spec.get_largest_constant());

	std::size_t tree_size        = 0;
	std::size_t pruned_tree_size = 0;
	std::size_t controller_size  = 0;
	std::size_t plant_size       = 0;

	std::unique_ptr<search::Heuristic<long, TreeSearch::Node>> heuristic;

	for (auto _ : state) {
		switch (mode) {
		case Mode::SCALED:
			heuristic = generate_heuristic<TreeSearch::Node>(16, 4, environment_actions, 1);
			break;
		case Mode::WEIGHTED:
			heuristic = generate_heuristic<TreeSearch::Node>(state.range(0),
			                                                 state.range(1),
			                                                 environment_actions,
			                                                 state.range(2));
			break;
		case (Mode::SIMPLE):
			if (state.range(0) == 0) {
				heuristic = std::make_unique<search::BfsHeuristic<long, TreeSearch::Node>>();
			} else if (state.range(0) == 1) {
				heuristic = std::make_unique<search::DfsHeuristic<long, TreeSearch::Node>>();
			} else if (state.range(0) == 2) {
				heuristic = std::make_unique<search::NumCanonicalWordsHeuristic<long, TreeSearch::Node>>();
			} else if (state.range(0) == 3) {
				heuristic = std::make_unique<
				  search::PreferEnvironmentActionHeuristic<long, TreeSearch::Node, std::string>>(
				  environment_actions);
			} else if (state.range(0) == 4) {
				heuristic = std::make_unique<search::TimeHeuristic<long, TreeSearch::Node>>();
			} else if (state.range(0) == 5) {
				heuristic = std::make_unique<search::RandomHeuristic<long, TreeSearch::Node>>(time(NULL));
			} else {
				throw std::invalid_argument("Unexpected argument");
			}
			break;
		}
		TreeSearch search{
		  &plant, &ata, controller_actions, environment_actions, K, true, true, std::move(heuristic)};

		search.build_tree(multi_threaded);
		search.label();
		plant_size += plant.get_locations().size();
		tree_size += search.get_size();
		std::for_each(std::begin(search.get_nodes()),
		              std::end(search.get_nodes()),
		              [&pruned_tree_size](const auto &node) {
			              if (node.second->label != search::NodeLabel::CANCELED
			                  && node.second->label != search::NodeLabel::UNLABELED) {
				              pruned_tree_size += 1;
			              }
		              });
		auto controller = controller_synthesis::create_controller(
		  search.get_root(), controller_actions, environment_actions, K, true);
		controller_size += controller.get_locations().size();
	}
	state.counters["tree_size"] =
	  benchmark::Counter(static_cast<double>(tree_size), benchmark::Counter::kAvgIterations);
	state.counters["pruned_tree_size"] =
	  benchmark::Counter(static_cast<double>(pruned_tree_size), benchmark::Counter::kAvgIterations);
	state.counters["controller_size"] =
	  benchmark::Counter(static_cast<double>(controller_size), benchmark::Counter::kAvgIterations);
	state.counters["plant_size"] =
	  benchmark::Counter(static_cast<double>(plant_size), benchmark::Counter::kAvgIterations);
}

// Range all over all heuristics individually.
BENCHMARK_CAPTURE(BM_Railroad_zone, single_heuristic, Mode::SIMPLE)
  ->DenseRange(0, 5, 1)
  ->MeasureProcessCPUTime()
  ->Unit(benchmark::kSecond)
  ->UseRealTime();
// Single-threaded.
BENCHMARK_CAPTURE(BM_Railroad_zone, single_heuristic_single_thread, Mode::SIMPLE, false)
  ->DenseRange(0, 5, 1)
  ->MeasureProcessCPUTime()
  ->Unit(benchmark::kSecond)
  ->UseRealTime();
// Single-threaded with weighted heuristics.
BENCHMARK_CAPTURE(BM_Railroad_zone, weighted_single_thread, Mode::WEIGHTED, false)
  ->Args({16, 4, 1})
  ->MeasureProcessCPUTime()
  ->Unit(benchmark::kSecond)
  ->UseRealTime();
// Weighted heuristics.
BENCHMARK_CAPTURE(BM_Railroad_zone, weighted, Mode::WEIGHTED)
  ->ArgsProduct({benchmark::CreateRange(1, 16, 2),
                 benchmark::CreateRange(1, 16, 2),
                 benchmark::CreateDenseRange(0, 2, 1)})
  ->MeasureProcessCPUTime()
  ->Unit(benchmark::kSecond)
  ->UseRealTime();
// Different distances
BENCHMARK_CAPTURE(BM_Railroad_zone, scaled, Mode::SCALED)
  ->ArgsProduct({benchmark::CreateRange(1, 8, 2), benchmark::CreateRange(1, 8, 2), {0}})
  ->MeasureProcessCPUTime()
  ->Unit(benchmark::kSecond)
  ->UseRealTime();

#ifdef BUILD_LARGE_BENCHMARKS
BENCHMARK_CAPTURE(BM_Railroad_zone, scaled, Mode::SCALED)
  ->Args({1, 1, 1})
  ->Args({2, 1, 1})
  ->Args({2, 2, 2})
  ->MeasureProcessCPUTime()
  ->Unit(benchmark::kSecond)
  ->UseRealTime();
#endif

//~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~CONVEYOR BELT~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

static void
BM_ConveyorBelt_zone(benchmark::State &state, bool weighted = true, bool multi_threaded = true)
{
	Location l_no{"NO"};
	Location l_st{"ST"};
	Location l_sp{"SP"};

	std::set<std::string> environment_actions{"release", "resume", "stuck"};
	std::set<std::string> controller_actions{"move", "stop"};
	std::set<std::string> actions;
	std::set_union(std::begin(environment_actions),
	               std::end(environment_actions),
	               std::begin(controller_actions),
	               std::end(controller_actions),
	               std::inserter(actions, std::begin(actions)));

	// the conveyor belt plant
	TA plant{{l_no, l_st, l_sp},
	         actions,
	         l_no,
	         {l_no},
	         {"move_timer", "stuck_timer"},
	         {Transition{l_no,
	                     "move",
	                     l_no,
	                     {{"move_timer",
	                       automata::AtomicClockConstraintT<std::greater_equal<Time>>{1}}},
	                     {"move_timer"}},
	          Transition{l_no, "stuck", l_st, {}, {"stuck_timer"}},
	          Transition{l_no, "stop", l_sp},
	          Transition{l_st, "release", l_no},
	          Transition{l_sp, "resume", l_no}}};

	// the specification
	const auto move_f    = F{AP{"move"}};
	const auto release_f = F{AP{"release"}};
	const auto stuck_f   = F{AP{"stuck"}};
	const auto stop_f    = F{AP{"stop"}};
	const auto resume_f  = F{AP{"resume"}};
	const auto spec      = finally(release_f && finally(move_f, logic::TimeInterval(0, 2)))
	                  || finally(stop_f && (!stuck_f).until(stop_f)) || (!stuck_f).until(stop_f);
	// || finally(globally(!move_f)); // cannot be satisfied as we cannot enforce 'release'

	auto ata = mtl_ata_translation::translate(
	  spec, {AP{"move"}, AP{"release"}, AP{"stuck"}, AP{"stop"}, AP{"resume"}});
	const unsigned int K = std::max(plant.get_largest_constant(), spec.get_largest_constant());

	std::size_t tree_size        = 0;
	std::size_t pruned_tree_size = 0;
	std::size_t controller_size  = 0;
	std::size_t plant_size       = 0;

	for (auto _ : state) {
		std::unique_ptr<search::Heuristic<long, CBTreeSearch::Node>> heuristic;
		if (weighted) {
			heuristic = generate_heuristic<CBTreeSearch::Node>(state.range(0),
			                                                 state.range(1),
			                                                 environment_actions,
			                                                 state.range(2));
		} else {
			if (state.range(0) == 0) {
				heuristic = std::make_unique<search::BfsHeuristic<long, CBTreeSearch::Node>>();
			} else if (state.range(0) == 1) {
				heuristic = std::make_unique<search::DfsHeuristic<long, CBTreeSearch::Node>>();
			} else if (state.range(0) == 2) {
				heuristic = std::make_unique<search::NumCanonicalWordsHeuristic<long, CBTreeSearch::Node>>();
			} else if (state.range(0) == 3) {
				heuristic = std::make_unique<
				  search::PreferEnvironmentActionHeuristic<long, CBTreeSearch::Node, std::string>>(
				  environment_actions);
			} else if (state.range(0) == 4) {
				heuristic = std::make_unique<search::TimeHeuristic<long, CBTreeSearch::Node>>();
			} else if (state.range(0) == 5) {
				heuristic = std::make_unique<search::RandomHeuristic<long, CBTreeSearch::Node>>(time(NULL));
			} else {
				throw std::invalid_argument("Unexpected argument");
			}
		}
		CBTreeSearch search{&plant,
		                  &ata,
		                  controller_actions,
		                  environment_actions,
		                  K,
		                  true,
		                  true,
		                  generate_heuristic<CBTreeSearch::Node>()};
		search.build_tree(multi_threaded);
		search.label();
		auto controller = controller_synthesis::create_controller(search.get_root(),
		                                                          controller_actions,
		                                                          environment_actions,
		                                                          K);
		tree_size += search.get_size();
		std::for_each(std::begin(search.get_nodes()),
		              std::end(search.get_nodes()),
		              [&pruned_tree_size](const auto &node) {
			              if (node.second->label != search::NodeLabel::CANCELED
			                  && node.second->label != search::NodeLabel::UNLABELED) {
				              pruned_tree_size += 1;
			              }
		              });
		plant_size += plant.get_locations().size();
		controller_size += controller.get_locations().size();
	}

	state.counters["tree_size"] =
	  benchmark::Counter(static_cast<double>(tree_size), benchmark::Counter::kAvgIterations);
	state.counters["pruned_tree_size"] =
	  benchmark::Counter(static_cast<double>(pruned_tree_size), benchmark::Counter::kAvgIterations);
	state.counters["controller_size"] =
	  benchmark::Counter(static_cast<double>(controller_size), benchmark::Counter::kAvgIterations);
	state.counters["plant_size"] =
	  benchmark::Counter(static_cast<double>(plant_size), benchmark::Counter::kAvgIterations);
}

BENCHMARK_CAPTURE(BM_ConveyorBelt_zone, single_heuristic, false)
  ->DenseRange(0, 5, 1)
  ->MeasureProcessCPUTime()
  ->Unit(benchmark::kSecond)
  ->UseRealTime();
BENCHMARK_CAPTURE(BM_ConveyorBelt_zone, single_heuristic_single_thread, false, false)
  ->DenseRange(0, 5, 1)
  ->MeasureProcessCPUTime()
  ->Unit(benchmark::kSecond)
  ->UseRealTime();
// Single-threaded with weighted heuristics.
BENCHMARK_CAPTURE(BM_ConveyorBelt_zone, weighted_single_thread, true, false)
  ->Args({16, 4, 1})
  ->MeasureProcessCPUTime()
  ->Unit(benchmark::kSecond)
  ->UseRealTime();
BENCHMARK_CAPTURE(BM_ConveyorBelt_zone, weighted, true)
  ->ArgsProduct({benchmark::CreateRange(1, 16, 2),
                 benchmark::CreateRange(1, 16, 2),
                 benchmark::CreateDenseRange(0, 2, 1)})
  ->MeasureProcessCPUTime()
  ->Unit(benchmark::kSecond)
  ->UseRealTime();
