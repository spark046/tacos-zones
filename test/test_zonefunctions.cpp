#include "automata/automata.h"
#include "automata/automata_zones.h"
#include "automata/ta.h"
#include "automata/ta_product.h"
#include "automata/ta_regions.h"
#include "utilities/types.h"
#include "automata/ta_regions.h"

#include "search/search.h"


//TODO: Figure out what is actually necessary, currently just copied from test_railroad.cpp
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

#include <catch2/benchmark/catch_benchmark.hpp>
#include <catch2/generators/catch_generators.hpp>
#include <catch2/catch_test_macros.hpp>
#include <map>
#include <string>

namespace {

using namespace tacos;

using Configuration  = automata::ta::TAConfiguration<std::string>;
using TimedAutomaton = automata::ta::TimedAutomaton<std::string, std::string>;
using TATransition   = automata::ta::Transition<std::string, std::string>;
using Location       = automata::ta::Location<std::string>;

using AlternatingTimedAutomaton = automata::ata::AlternatingTimedAutomaton<std::string, std::string>;
using ATATransition             = automata::ata::Transition<std::string, std::string>;
using Formula                   = automata::ata::Formula<std::string>;
using TrueFormula               = automata::ata::TrueFormula<std::string>;
using FalseFormula              = automata::ata::FalseFormula<std::string>;
using LocationFormula           = automata::ata::LocationFormula<std::string>;
using ClockConstraintFormula    = automata::ata::ClockConstraintFormula<std::string>;
using ConjunctionFormula        = automata::ata::ConjunctionFormula<std::string>;
using DisjunctionFormula        = automata::ata::DisjunctionFormula<std::string>;
using ResetClockFormula         = automata::ata::ResetClockFormula<std::string>;

using AP                        = logic::AtomicProposition<std::string>;
using Plant = automata::ta::TimedAutomaton<std::vector<std::string>, std::string>;
using TreeSearch =
  search::TreeSearch<automata::ta::Location<std::vector<std::string>>, std::string, std::string, false, Plant, false, RegionIndex>;

using PlantZoneState = search::PlantZoneState<Location>;
using ATAZoneState = search::ATAZoneState<std::string>;
using CanonicalABWord = search::CanonicalABWord<automata::ta::Location<std::string>, std::string>;
using ATAConfiguration = automata::ata::Configuration<logic::MTLFormula<std::string>>;

TEST_CASE("Getting fulfilled Clock Constraints of a ta", "[zones]")
{
	automata::ClockConstraint c1 = automata::AtomicClockConstraintT<std::less<Time>>(1);
	automata::ClockConstraint c2 = automata::AtomicClockConstraintT<std::greater<Time>>(1);
	automata::ClockConstraint c3 = automata::AtomicClockConstraintT<std::equal_to<Time>>(1);

	TimedAutomaton ta{{"a", "b"}, Location{"s0"}, {Location{"s0"}, Location{"s1"}}};
	ta.add_clock("x");
	ta.add_transition(TATransition(Location{"s0"}, "a", Location{"s0"}, {{"x", c1}, {"x", c2}}));
	ta.add_transition(TATransition(Location{"s0"}, "b", Location{"s1"}, {{"x", c3}}));

	std::multimap<std::string, automata::ClockConstraint> set1 = {{"x", c1}, {"x", c2}, {"x", c3}};
	std::multimap<std::string, automata::ClockConstraint> set2 = {{"x", c1}};

	CHECK(ta.get_clock_constraints() == set1);

	CHECK(zones::get_fulfilled_clock_constraints(ta.get_clock_constraints(), "x", 0) == set2);
}

TEST_CASE("Delaying zones of zone states", "[zones]")
{
	std::multimap<std::string, automata::ClockConstraint> constraint1 = {{"x", automata::AtomicClockConstraintT<std::greater<Time>>(1)}};
	zones::Zone_slice zone1 = zones::Zone_slice(constraint1, "x");

	std::multimap<std::string, automata::ClockConstraint> constraint2 = { {"x", automata::AtomicClockConstraintT<std::greater<Time>>(1)},
																	{"x", automata::AtomicClockConstraintT<std::less<Time>>(2)}};
	
	//zones::Zone_slice zone2 = zones::Zone_slice(constraint2, "x");

	std::multimap<std::string, automata::ClockConstraint> constraint3 = { {"x", automata::AtomicClockConstraintT<std::equal_to<Time>>(1)},
																	{"x", automata::AtomicClockConstraintT<std::less_equal<Time>>(2)}};

	//zones::Zone_slice zone3 = zones::Zone_slice(constraint3, "x");

	std::multimap<std::string, automata::ClockConstraint> constraint4 = { {"x", automata::AtomicClockConstraintT<std::greater_equal<Time>>(1)}};

	zones::Zone_slice zone4 = zones::Zone_slice(constraint4, "x");

	search::PlantZoneState<std::string> ta_state1 = {"l0", "x", constraint1};
	CHECK(ta_state1.get_increment_valuation() == zone1);

	search::PlantZoneState<std::string> ta_state2 = {"l0", "x", constraint2};
	CHECK(ta_state2.get_increment_valuation() == zone1);

	search::PlantZoneState<std::string> ta_state3 = {"l0", "x", constraint3};
	CHECK(ta_state3.get_increment_valuation() == zone4);
}

TEST_CASE("Getting Clock Constraints from ATA", "[zones]")
{
	automata::ClockConstraint constraint1 = automata::AtomicClockConstraintT<std::less<Time>>(1);
	automata::ClockConstraint constraint2 = automata::AtomicClockConstraintT<std::equal_to<Time>>(3);
	automata::ClockConstraint constraint3 = automata::AtomicClockConstraintT<std::greater_equal<Time>>(0);
	automata::ClockConstraint constraint4 = automata::AtomicClockConstraintT<std::greater<Time>>(5);
	automata::ClockConstraint constraint5 = automata::AtomicClockConstraintT<std::less_equal<Time>>(10);

	std::set<ATATransition> transitions;

	transitions.insert(ATATransition(
		"s0", "a", std::make_unique<TrueFormula>()));

	transitions.insert(ATATransition(
		"s0", "a", std::make_unique<FalseFormula>()));

	transitions.insert(ATATransition(
		"s0", "a", std::make_unique<LocationFormula>("s0")));

	transitions.insert(ATATransition(
		"s0", "a", std::make_unique<ClockConstraintFormula>(constraint1)));

	transitions.insert(ATATransition(
		"s0", "a", std::make_unique<ConjunctionFormula>(
			std::make_unique<ClockConstraintFormula>(constraint2),
			std::make_unique<ClockConstraintFormula>(constraint3)
		)));

	transitions.insert(ATATransition(
		"s0", "a", std::make_unique<DisjunctionFormula>(
			std::make_unique<ClockConstraintFormula>(constraint3),
			std::make_unique<ClockConstraintFormula>(constraint4)
		)));

	transitions.insert(ATATransition(
		"s0", "a", std::make_unique<ResetClockFormula>(
			std::make_unique<ClockConstraintFormula>(constraint5)
		)));
	
	AlternatingTimedAutomaton ata({"a"},
								  "s0",
								  {"s0"},
								  std::move(transitions));

	std::set<automata::ClockConstraint> all_clock_constraints = ata.get_clock_constraints();

	CHECK(all_clock_constraints == std::set<automata::ClockConstraint>{constraint1, constraint2, constraint3, constraint4, constraint5});
}

TEST_CASE("Canonical Word using zones", "[zones]")
{
	TimedAutomaton ta{{Location{"s0"}, Location{"s1"}, Location{"s2"}},
		  {"a", "b", "c"},
		  Location{"s0"},
		  {Location{"s0"}, Location{"s1"}, Location{"s2"}},
		  {"x"},
		  {TATransition(Location{"s0"},
						"a",
						Location{"s0"},
						{{"x", automata::AtomicClockConstraintT<std::greater<Time>>(1)}},
						{"x"}),
		   TATransition(Location{"s0"},
						"b",
						Location{"s1"},
						{{"x", automata::AtomicClockConstraintT<std::less<Time>>(1)}}),
		   TATransition(Location{"s0"}, "c", Location{"s2"}),
		   TATransition(Location{"s2"}, "b", Location{"s1"})}};


	logic::MTLFormula<std::string> a{AP("a")};
	logic::MTLFormula<std::string> b{AP("b")};
	logic::MTLFormula f   = a.until(b);
	auto              ata = mtl_ata_translation::translate(f);

	std::multimap<std::string, automata::ClockConstraint> clock_constraints = {
																				{"x", automata::AtomicClockConstraintT<std::greater<Time>>(1)},
																				{"x", automata::AtomicClockConstraintT<std::less<Time>>(1)}
																			  };

	auto initial_word = search::get_canonical_word(Configuration{Location{"s0"}, {{"x", 0}}},
										   ata.get_initial_configuration(),
										   2,
										   true,
										   clock_constraints);


	zones::Zone_slice zone_everything = zones::Zone_slice{0, 2, false, false, 2};
	zones::Zone_slice zone_less1 = zones::Zone_slice{0, 1, false, true, 2};
	//zones::Zone_slice zone_greater1 = zones::Zone_slice{1, 2, true, false, 2};

	CHECK(!search::is_region_canonical_word(initial_word));

	CHECK(initial_word
			  == CanonicalABWord({{PlantZoneState{Location{"s0"}, "x", zone_less1},
								   ATAZoneState{logic::MTLFormula{AP{"l0"}}, zone_everything}}}));

	CHECK(search::get_next_canonical_words<TimedAutomaton, std::string, std::string, false>()(
				ta, ata, {ta.get_initial_configuration(), ata.get_initial_configuration()}, 0, 2, true)
			  == std::multimap<std::string, CanonicalABWord>{
				{"b", CanonicalABWord{{PlantZoneState{Location{"s1"}, "x", zone_less1}, ATAZoneState{f, zone_everything}}}},
				{"c",
				 CanonicalABWord{{PlantZoneState{Location{"s2"}, "x", zone_less1},
								  ATAZoneState{mtl_ata_translation::get_sink<std::string>(), zone_everything}}}}});
	
	CHECK(search::get_next_canonical_words<TimedAutomaton, std::string, std::string, false>()(
				ta, ata, {ta.get_initial_configuration(), ATAConfiguration{{f, 0}}}, 0, 2, true)
			  == std::multimap<std::string, CanonicalABWord>{
				{"b", CanonicalABWord{{PlantZoneState{Location{"s1"}, "x", zone_less1}}}},
				{"c",
				 CanonicalABWord{{PlantZoneState{Location{"s2"}, "x", zone_less1},
								  ATAZoneState{mtl_ata_translation::get_sink<std::string>(), zone_everything}}}}});
}

TEST_CASE("monotone_domination_order for zones", "[zones]")
{
	zones::Zone_slice zone0 = zones::Zone_slice{0, std::numeric_limits<Endpoint>::max(), false, false};
	zones::Zone_slice zone1 = zones::Zone_slice{1, std::numeric_limits<Endpoint>::max(), false, false};

	CHECK(search::is_monotonically_dominated(
	  CanonicalABWord({{PlantZoneState{Location{"s0"}, "c0", zone0}}}),
	  CanonicalABWord({{PlantZoneState{Location{"s0"}, "c0", zone0}}})));
	CHECK(!search::is_monotonically_dominated(
	  CanonicalABWord({{PlantZoneState{Location{"s0"}, "c0", zone0}}}),
	  CanonicalABWord({{PlantZoneState{Location{"s0"}, "c0", zone1}}})));
	CHECK(!search::is_monotonically_dominated(
	  CanonicalABWord(
		{{PlantZoneState{Location{"s0"}, "c0", zone0}, ATAZoneState{logic::MTLFormula{AP{"a"}}, zone0}}}),
	  CanonicalABWord({{PlantZoneState{Location{"s0"}, "c0", zone0}}})));
	CHECK(search::is_monotonically_dominated(
	  CanonicalABWord(
		{{PlantZoneState{Location{"s0"}, "c0", zone0}, PlantZoneState{Location{"s0"}, "c1", zone0}}}),
	  CanonicalABWord(
		{{PlantZoneState{Location{"s0"}, "c0", zone0}, PlantZoneState{Location{"s0"}, "c1", zone0}}})));
	CHECK(!search::is_monotonically_dominated(
	  CanonicalABWord(
		{{PlantZoneState{Location{"s0"}, "c0", zone0}, PlantZoneState{Location{"s0"}, "c1", zone1}},
		 {ATAZoneState{logic::MTLFormula{AP{"a"}}, zone0}}}),
	  CanonicalABWord(
		{{PlantZoneState{Location{"s0"}, "c0", zone0}, PlantZoneState{Location{"s0"}, "c1", zone1}}})));
	CHECK(search::is_monotonically_dominated(
	  CanonicalABWord(
		{{PlantZoneState{Location{"s0"}, "c0", zone0}, PlantZoneState{Location{"s0"}, "c1", zone1}}}),
	  CanonicalABWord(
		{{PlantZoneState{Location{"s0"}, "c0", zone0}, PlantZoneState{Location{"s0"}, "c1", zone1}},
		 {ATAZoneState{logic::MTLFormula{AP{"a"}}, zone0}}})));
	CHECK(search::is_monotonically_dominated(
	  CanonicalABWord({{PlantZoneState{Location{"s0"}, "c0", zone0}}}),
	  CanonicalABWord(
		{{PlantZoneState{Location{"s0"}, "c0", zone0}, PlantZoneState{Location{"s0"}, "c1", zone1}},
		 {ATAZoneState{logic::MTLFormula{AP{"a"}}, zone0}}})));
}

TEST_CASE("Get time successors of CanonicalABWords using zones", "[zones]")
{
	zones::Zone_slice zone_all = zones::Zone_slice{0, 3, false, false, 3};
	zones::Zone_slice zone_gtr_0 = zones::Zone_slice{0, 3, true, false, 3};
	zones::Zone_slice zone_geq_1 = zones::Zone_slice{1, 3, false, false, 3};
	zones::Zone_slice zone_gtr_1 = zones::Zone_slice{1, 3, true, false, 3};

	// TODO rewrite test cases to only contain valid words
	CHECK(get_time_successor(CanonicalABWord({{PlantZoneState{Location{"s0"}, "c0", zone_all}},
											  {PlantZoneState{Location{"s0"}, "c1", zone_gtr_0}}}),
							 3)
		  == CanonicalABWord(
			{{PlantZoneState{Location{"s0"}, "c0", zone_gtr_0}}, {PlantZoneState{Location{"s0"}, "c1", zone_gtr_0}}}));
	CHECK(get_time_successor(CanonicalABWord({{PlantZoneState{Location{"s0"}, "c0", zone_all}}}), 3)
		  == CanonicalABWord({{PlantZoneState{Location{"s0"}, "c0", zone_gtr_0}}}));
	CHECK(get_time_successor(CanonicalABWord({{PlantZoneState{Location{"s0"}, "c0", zone_all}},
											  {PlantZoneState{Location{"s0"}, "c1", zone_gtr_0}},
											  {PlantZoneState{Location{"s0"}, "c2", zone_geq_1}}}),
							 3)
		  == CanonicalABWord({{PlantZoneState{Location{"s0"}, "c0", zone_gtr_0}},
							  {PlantZoneState{Location{"s0"}, "c1", zone_gtr_0}},
							  {PlantZoneState{Location{"s0"}, "c2", zone_geq_1}}}));
	CHECK(get_time_successor(CanonicalABWord({{PlantZoneState{Location{"s0"}, "c0", zone_gtr_0}},
											  {PlantZoneState{Location{"s0"}, "c1", zone_geq_1}}}),
							 3)
		  == CanonicalABWord(
			{{PlantZoneState{Location{"s0"}, "c1", zone_gtr_1}}, {PlantZoneState{Location{"s0"}, "c0", zone_gtr_0}}}));
	
	//TODO: Refactor all tests
	#if false
	CHECK(get_time_successor(CanonicalABWord({{PlantZoneState{Location{"s0"}, "c0", 1}},
											  {PlantZoneState{Location{"s0"}, "c1", 1}}}),
							 3)
		  == CanonicalABWord(
			{{PlantZoneState{Location{"s0"}, "c1", 2}}, {PlantZoneState{Location{"s0"}, "c0", 1}}}));
	const logic::AtomicProposition<std::string> a{"a"};
	const logic::AtomicProposition<std::string> b{"b"};
	CHECK(get_time_successor(CanonicalABWord({{ATAZoneState{a, 0}},
											  {ATAZoneState{b, 1}},
											  {ATAZoneState{a || b, 3}}}),
							 3)
		  == CanonicalABWord(
			{{ATAZoneState{a, 1}}, {ATAZoneState{b, 1}}, {ATAZoneState{a || b, 3}}}));
	CHECK(get_time_successor(CanonicalABWord({{ATAZoneState{a, 7}}}), 3)
		  == CanonicalABWord({{ATAZoneState{a, 7}}}));
	CHECK(get_time_successor(CanonicalABWord({{ATAZoneState{b, 3}}, {ATAZoneState{a, 7}}}), 3)
		  == CanonicalABWord({{ATAZoneState{b, 4}}, {ATAZoneState{a, 7}}}));

	CHECK(get_time_successor(CanonicalABWord({{ATAZoneState{b, 3}, ATAZoneState{a, 7}}}), 3)
		  == CanonicalABWord({{ATAZoneState{b, 4}}, {ATAZoneState{a, 7}}}));

	CHECK(get_time_successor(CanonicalABWord({{PlantZoneState{Location{"s1"}, "c0", 4}},
											  {PlantZoneState{Location{"s0"}, "c0", 3}},
											  {ATAZoneState{a, 7}}}),
							 3)
		  == CanonicalABWord({{PlantZoneState{Location{"s1"}, "c0", 5}},
							  {PlantZoneState{Location{"s0"}, "c0", 3}},
							  {ATAZoneState{a, 7}}}));
	CHECK(get_time_successor(CanonicalABWord({{ATAZoneState{b, 1}, ATAZoneState{a, 3}}}), 3)
		  == CanonicalABWord({{ATAZoneState{b, 2}, ATAZoneState{a, 4}}}));
	CHECK(get_time_successor(
			CanonicalABWord({{PlantZoneState{Location{"l0"}, "x", 1}, ATAZoneState{a, 5}}}), 2)
		  == CanonicalABWord({{PlantZoneState{Location{"l0"}, "x", 2}}, {ATAZoneState{a, 5}}}));

	CHECK(get_time_successor(CanonicalABWord{{PlantZoneState{Location{"l0"}, "x0", 0}},
											 {PlantZoneState{Location{"l0"}, "x1", 1}},
											 {PlantZoneState{Location{"l0"}, "x3", 3}}},
							 1)
		  == CanonicalABWord{{PlantZoneState{Location{"l0"}, "x0", 1}},
							 {PlantZoneState{Location{"l0"}, "x1", 1}},
							 {PlantZoneState{Location{"l0"}, "x3", 3}}});
	// x2 is incremented and should end up in the last partition with the maxed regions.
	CHECK(get_time_successor(CanonicalABWord{{PlantZoneState{Location{"l0"}, "x2", 2}},
											 {PlantZoneState{Location{"l0"}, "x3", 3}}},
							 1)
		  == CanonicalABWord{
			{PlantZoneState{Location{"l0"}, "x2", 3}, PlantZoneState{Location{"l0"}, "x3", 3}}});
	CHECK(get_time_successor(CanonicalABWord{{PlantZoneState{Location{"l0"}, "x0", 0},
											  PlantZoneState{Location{"l0"}, "x2", 2}},
											 {PlantZoneState{Location{"l0"}, "x1", 1}},
											 {PlantZoneState{Location{"l0"}, "x3", 3}}},
							 1)
		  == CanonicalABWord{{PlantZoneState{Location{"l0"}, "x0", 1}},
							 {PlantZoneState{Location{"l0"}, "x1", 1}},
							 {PlantZoneState{Location{"l0"}, "x2", 3},
							  PlantZoneState{Location{"l0"}, "x3", 3}}});

	// Both x0 and x2 are incremented and should be split. x2 should end up in the maxed partition
	// with x3.
	CHECK(get_time_successor(CanonicalABWord{{PlantZoneState{Location{"l0"}, "x0", 0},
											  PlantZoneState{Location{"l0"}, "x2", 2}},
											 {PlantZoneState{Location{"l0"}, "x3", 3}}},
							 1)
		  == CanonicalABWord{{PlantZoneState{Location{"l0"}, "x0", 1}},
							 {PlantZoneState{Location{"l0"}, "x2", 3},
							  PlantZoneState{Location{"l0"}, "x3", 3}}});

	// Successor of successor.
	CHECK(get_time_successor(
			get_time_successor(CanonicalABWord({{PlantZoneState{Location{"s0"}, "c0", 0}}}), 3), 3)
		  == CanonicalABWord({{PlantZoneState{Location{"s0"}, "c0", 2}}}));
	CHECK(search::get_nth_time_successor(CanonicalABWord({{PlantZoneState{Location{"s0"}, "c0", 0}}}),
										 2,
										 3)
		  == CanonicalABWord({{PlantZoneState{Location{"s0"}, "c0", 2}}}));
	CHECK(search::get_nth_time_successor(CanonicalABWord({{PlantZoneState{Location{"s0"}, "c0", 0}}}),
										 0,
										 3)
		  == CanonicalABWord({{PlantZoneState{Location{"s0"}, "c0", 0}}}));
	CHECK(search::get_nth_time_successor(CanonicalABWord({{PlantZoneState{Location{"s0"}, "c0", 0}}}),
										 7,
										 3)
		  == search::get_nth_time_successor(
			CanonicalABWord({{PlantZoneState{Location{"s0"}, "c0", 0}}}), 8, 3));
	CHECK(get_time_successor(CanonicalABWord{{ATAZoneState{a, 0}},
											 {PlantZoneState{Location{"s0"}, "c0", 1}}},
							 1)
		  == CanonicalABWord{{ATAZoneState{a, 1}}, {PlantZoneState{Location{"s0"}, "c0", 1}}});
	CHECK(get_time_successor(CanonicalABWord{{ATAZoneState{a, 1}},
											 {PlantZoneState{Location{"s0"}, "c0", 1}}},
							 1)
		  == CanonicalABWord{{PlantZoneState{Location{"s0"}, "c0", 2}}, {ATAZoneState{a, 1}}});
	#endif
}

#if true
TEST_CASE("Railroad example using zones", "[zones]")
{
	const auto &[plant, spec, controller_actions, environment_actions] = create_crossing_problem({2});
	//const auto   num_crossings                                         = 1;
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
	TreeSearch search{&plant,
					  &ata,
					  controller_actions,
					  environment_actions,
					  K,
					  true,
					  true,
					  generate_heuristic<TreeSearch::Node>(),
					  true};
	search.build_tree(true);
	CHECK(search.get_root()->label == search::NodeLabel::TOP);

	#if true
	const int num_crossings = 2;
	visualization::search_tree_to_graphviz(*search.get_root(), true)
	  .render_to_file(fmt::format("railroad{}.svg", num_crossings));
	visualization::ta_to_graphviz(controller_synthesis::create_controller(
									search.get_root(), controller_actions, environment_actions, 2),
								  false)
	  .render_to_file(fmt::format("railroad{}_controller.pdf", num_crossings));
	#endif
}
#endif

} // namespace

