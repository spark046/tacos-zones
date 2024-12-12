#include "automata/automata.h"
#include "automata/automata_zones.h"
#include "automata/ta.h"
#include "automata/ta_product.h"
#include "utilities/types.h"

#include "search/search.h"
#include "search/verify_ta_controller.h"
#include "search/ta_adapter.h"


//TODO: Figure out what is actually necessary, currently just copied from test_railroad.cpp
#include "heuristics_generator.h"
#include "mtl/MTLFormula.h"
#include "mtl_ata_translation/translator.h"
#include "railroad.h"
#include "search/canonical_word.h"
#include "search/create_controller.h"
#include "visualization/ta_to_graphviz.h"
#include "visualization/tree_to_graphviz.h"
#include "visualization/interactive_tree_to_graphviz.h"

#include <catch2/benchmark/catch_benchmark.hpp>
#include <catch2/generators/catch_generators.hpp>
#include <catch2/catch_test_macros.hpp>
#include <map>
#include <string>

#define USE_VISUALIZATION_INCONSISTENCY true

namespace {
	using namespace tacos;

	TEST_CASE("1000 Railroad example using zones with multi-threading", "[zones]")
	{
		using AP = logic::AtomicProposition<std::string>;
		using TreeSearch =
			search::ZoneTreeSearch<automata::ta::Location<std::vector<std::string>>, std::string>;

		int iterations = 1000;
		int fail_count = 0;

		const auto &[plant, spec, controller_actions, environment_actions] = create_crossing_problem({2});
		std::set<AP> actions;
		std::set_union(begin(controller_actions),
					end(controller_actions),
					begin(environment_actions),
					end(environment_actions),
					inserter(actions, end(actions)));
		auto ata = mtl_ata_translation::translate(spec, actions);
		const unsigned int K = std::max(plant.get_largest_constant(), spec.get_largest_constant());

		for(int i = 0; i < iterations; i++) {
			TreeSearch search{&plant,
							&ata,
							controller_actions,
							environment_actions,
							K,
							true,
							true};
			
			search.build_tree(true);

			#if USE_VISUALIZATION_INCONSISTENCY
				auto visualization = visualization::search_tree_to_graphviz(*search.get_root(), false);
			#endif

			try {
				search.label();
			} catch(std::logic_error&) {
				fail_count++;

				#if USE_VISUALIZATION_INCONSISTENCY
					visualization.render_to_file(fmt::format("railroad_error_mt_{}.svg", i));
				#endif
				continue;
			}
			
			if(search.get_root()->label != search::NodeLabel::TOP) {
				try {
					throw std::runtime_error(fmt::format("Search Tree should be labelled TOP but is labelled {} in iteration {}", search.get_root()->label, i));
				} catch (std::runtime_error&) {
					#if USE_VISUALIZATION_INCONSISTENCY
						visualization::search_tree_to_graphviz(*search.get_root(), true)
						.render_to_file(fmt::format("railroad_wronglabel_mt_{}.svg", i));
					#endif

					fail_count++;
				}
			} else {
				auto controller = controller_synthesis::create_controller(
								search.get_root(), controller_actions, environment_actions, 2
								);

				if(!search::verify_ta_controller(plant, controller, spec, K)) {
					try{
						throw std::runtime_error(fmt::format("Synthesized controller is incorrect in iteration {}", i));
					} catch (std::runtime_error&) {
						#if USE_VISUALIZATION_INCONSISTENCY
						visualization::search_tree_to_graphviz(*search.get_root(), true)
							.render_to_file(fmt::format("railroad_incorrect_mt_{}.svg", i));

						visualization::ta_to_graphviz(controller,
													false)
							.render_to_file(fmt::format("railroad_controller__mt{}.pdf", i));
						#endif
						
						fail_count++;
					}
				}
			}
		}

		CHECK(fail_count == 0);
	}

	TEST_CASE("1000 Robots using zones and with multithreading", "[zones]")
	{
		using Search = search::ZoneTreeSearch<automata::ta::Location<std::vector<std::string>>, std::string>;
		using TA     = automata::ta::TimedAutomaton<std::string, std::string>;
		using MTLFormula = logic::MTLFormula<std::string>;
		using AP         = logic::AtomicProposition<std::string>;
		using automata::AtomicClockConstraintT;

		int iterations = 1000;
		int fail_count = 0;

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

		for (int i = 0; i < iterations; i++) {

			Search search(
			&product, &ata, camera_actions, robot_actions, K, true, true);
			search.build_tree(true);

			#if USE_VISUALIZATION_INCONSISTENCY
				auto visualization = visualization::search_tree_to_graphviz(*search.get_root(), false);
			#endif

			try {
				search.label();
			} catch(std::logic_error&) {
				fail_count++;

				#if USE_VISUALIZATION_INCONSISTENCY
					visualization.render_to_file(fmt::format("robot_error_mt_{}.svg", i));
				#endif
				continue;
			}
			
			if(search.get_root()->label != search::NodeLabel::TOP) {
				try {
					throw std::runtime_error(fmt::format("Search Tree should be labelled TOP but is labelled {}", search.get_root()->label));
				} catch (std::runtime_error&) {
					#if USE_VISUALIZATION_INCONSISTENCY
						visualization::search_tree_to_graphviz(*search.get_root(), true)
						.render_to_file(fmt::format("railroad_wronglabel_mt_{}.svg", i));
					#endif

					fail_count++;
				}
			} else {
				auto controller = controller_synthesis::create_controller(
								search.get_root(), camera_actions, robot_actions, 2
								);

				if(!search::verify_ta_controller(product, controller, spec, K)) {
					try{
						throw std::runtime_error(fmt::format("Synthesized controller is incorrect in iteration {}", i));
					} catch (std::runtime_error&) {
						#if USE_VISUALIZATION_INCONSISTENCY
						visualization::search_tree_to_graphviz(*search.get_root(), true)
							.render_to_file(fmt::format("robot_incorrect_mt_{}.svg", i));

						visualization::ta_to_graphviz(controller,
													false)
							.render_to_file(fmt::format("robot_controller_mt_{}.pdf", i));
						#endif
						
						fail_count++;
					}
				}
			}
		}

		CHECK(fail_count == 0);
	}

	TEST_CASE("1000 Robots using zones and without multithreading", "[zones]")
	{
		using Search = search::ZoneTreeSearch<automata::ta::Location<std::vector<std::string>>, std::string>;
		using TA     = automata::ta::TimedAutomaton<std::string, std::string>;
		using MTLFormula = logic::MTLFormula<std::string>;
		using AP         = logic::AtomicProposition<std::string>;
		using automata::AtomicClockConstraintT;

		int iterations = 1000;
		int fail_count = 0;

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

		for(int i = 0; i < iterations; i++) {
			Search search(
			&product, &ata, camera_actions, robot_actions, K, true, true);
			search.build_tree(false);
			
			#if USE_VISUALIZATION_INCONSISTENCY
				auto visualization = visualization::search_tree_to_graphviz(*search.get_root(), false);
			#endif

			try {
				search.label();
			} catch(std::logic_error&) {
				fail_count++;

				#if USE_VISUALIZATION_INCONSISTENCY
					visualization.render_to_file(fmt::format("robot_error_st_{}.svg", i));
				#endif
				continue;
			}
			
			if(search.get_root()->label != search::NodeLabel::TOP) {
				try {
					throw std::runtime_error(fmt::format("Search Tree should be labelled TOP but is labelled {}", search.get_root()->label));
				} catch (std::runtime_error&) {
					#if USE_VISUALIZATION_INCONSISTENCY
						visualization::search_tree_to_graphviz(*search.get_root(), true)
						.render_to_file(fmt::format("railroad_wronglabel_mt_{}.svg", i));
					#endif

					fail_count++;
				}
			} else {
				auto controller = controller_synthesis::create_controller(
								search.get_root(), camera_actions, robot_actions, 2
								);

				if(!search::verify_ta_controller(product, controller, spec, K)) {
					try{
						throw std::runtime_error(fmt::format("Synthesized controller is incorrect in iteration {}", i));
					} catch (std::runtime_error&) {
						#if USE_VISUALIZATION_INCONSISTENCY
						visualization::search_tree_to_graphviz(*search.get_root(), true)
							.render_to_file(fmt::format("robot_incorrect_st_{}.svg", i));

						visualization::ta_to_graphviz(controller,
													false)
							.render_to_file(fmt::format("robot_controller_st_{}.pdf", i));
						#endif
						
						fail_count++;
					}
				}
			}
		}

		CHECK(fail_count == 0);
	}

	TEST_CASE("1000 Railroad example using zones without multi-threading", "[zones]")
	{
		using AP = logic::AtomicProposition<std::string>;
		using TreeSearch =
			search::ZoneTreeSearch<automata::ta::Location<std::vector<std::string>>, std::string>;

		int iterations = 1000;
		int fail_count = 0;

		const auto &[plant, spec, controller_actions, environment_actions] = create_crossing_problem({2});
		[[maybe_unused]] const int num_crossings = 2;
		std::set<AP> actions;
		std::set_union(begin(controller_actions),
					end(controller_actions),
					begin(environment_actions),
					end(environment_actions),
					inserter(actions, end(actions)));
		auto ata = mtl_ata_translation::translate(spec, actions);
		const unsigned int K = std::max(plant.get_largest_constant(), spec.get_largest_constant());

		for(int i = 0; i < iterations; i++) {
			TreeSearch search{&plant,
							&ata,
							controller_actions,
							environment_actions,
							K,
							true,
							true};
			
			search.build_tree(false);
			
			#if USE_VISUALIZATION_INCONSISTENCY
				auto visualization = visualization::search_tree_to_graphviz(*search.get_root(), false);
			#endif

			try {
				search.label();
			} catch(std::logic_error&) {
				fail_count++;

				#if USE_VISUALIZATION_INCONSISTENCY
					visualization.render_to_file(fmt::format("railroad_error_st_{}.svg", i));
				#endif
				continue;
			}
			
			if(search.get_root()->label != search::NodeLabel::TOP) {
				try {
					throw std::runtime_error(fmt::format("Search Tree should be labelled TOP but is labelled {}", search.get_root()->label));
				} catch (std::runtime_error&) {
					#if USE_VISUALIZATION_INCONSISTENCY
						visualization::search_tree_to_graphviz(*search.get_root(), true)
						.render_to_file(fmt::format("railroad_wronglabel_mt_{}.svg", i));
					#endif

					fail_count++;
				}
			} else {
				auto controller = controller_synthesis::create_controller(
								search.get_root(), controller_actions, environment_actions, 2
								);

				if(!search::verify_ta_controller(plant, controller, spec, K)) {
					try{
						throw std::runtime_error(fmt::format("Synthesized controller is incorrect in iteration {}", i));
					} catch (std::runtime_error&) {
						#if USE_VISUALIZATION_INCONSISTENCY
						visualization::search_tree_to_graphviz(*search.get_root(), true)
							.render_to_file(fmt::format("railroad_incorrect_st_{}.svg", i));

						visualization::ta_to_graphviz(controller,
													false)
							.render_to_file(fmt::format("railroad_controller__st{}.pdf", i));
						#endif
						
						fail_count++;
					}
				}
			}
		}

		CHECK(fail_count == 0);
	}

} //namespace