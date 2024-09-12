#include "automata/automata.h"
#include "automata/automata_zones.h"
#include "automata/ta.h"
#include "automata/ta_product.h"
#include "utilities/types.h"

#include "search/search.h"
#include "search/verify_ta_controller.h"


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

//Bugs with overflow?
#define ZONE_INFTY 30000

#define USE_INTERACTIVE_VISUALIZATION false

namespace {

using namespace tacos;

//using Configuration  = automata::ta::TAConfiguration<std::string>;
//using TimedAutomaton = automata::ta::TimedAutomaton<std::string, std::string>;
//using TATransition   = automata::ta::Transition<std::string, std::string>;
//using Location       = automata::ta::Location<std::string>;
//
//using AlternatingTimedAutomaton = automata::ata::AlternatingTimedAutomaton<std::string, std::string>;
//using ATATransition             = automata::ata::Transition<std::string, std::string>;
//using Formula                   = automata::ata::Formula<std::string>;
//using TrueFormula               = automata::ata::TrueFormula<std::string>;
//using FalseFormula              = automata::ata::FalseFormula<std::string>;
//using LocationFormula           = automata::ata::LocationFormula<std::string>;
//using ClockConstraintFormula    = automata::ata::ClockConstraintFormula<std::string>;
//using ConjunctionFormula        = automata::ata::ConjunctionFormula<std::string>;
//using DisjunctionFormula        = automata::ata::DisjunctionFormula<std::string>;
//using ResetClockFormula         = automata::ata::ResetClockFormula<std::string>;
//
//using AP                        = logic::AtomicProposition<std::string>;
//using TreeSearch =
//  search::TreeSearch<automata::ta::Location<std::vector<std::string>>, std::string>;
//
//using PlantZoneState = search::PlantZoneState<Location>;
//using ATAZoneState = search::ATAZoneState<std::string>;
//using CanonicalABWord = search::CanonicalABWord<automata::ta::Location<std::string>, std::string>;
//using ATAConfiguration = automata::ata::Configuration<logic::MTLFormula<std::string>>;

TEST_CASE("Getting fulfilled Clock Constraints of a ta", "[zones]")
{
	using TimedAutomaton = automata::ta::TimedAutomaton<std::string, std::string>;
	using TATransition   = automata::ta::Transition<std::string, std::string>;
	using Location       = automata::ta::Location<std::string>;

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

//Testing the weird 32767 Bug. Gave up and went for botched solution
TEST_CASE("Zone_slice functions", "[zones]")
{
	automata::ClockConstraint constraint1 = automata::AtomicClockConstraintT<std::greater<Time>>(1);

	zones::Zone_slice zone1{constraint1, ZONE_INFTY};

	CHECK(zone1.upper_bound_ == ZONE_INFTY);

	zones::Zone_slice zone2{constraint1, zone1.max_constant_};
	zone1.intersect(zone2);
	zone1.intersect(zone2);
	zone1.intersect(zone2);

	CHECK(zone1.upper_bound_ == ZONE_INFTY);

	zone1.conjunct(constraint1);

	CHECK(zone1.upper_bound_ == ZONE_INFTY);

	std::multimap<std::string, automata::ClockConstraint> constraint_map = {{"x", constraint1}};
	zones::Zone_slice zone3{constraint_map, "x", ZONE_INFTY};

	CHECK(zone1 == zone3);
}

TEST_CASE("Delaying zones of zone states", "[zones]")
{
	std::multimap<std::string, automata::ClockConstraint> constraint1 = {{"x", automata::AtomicClockConstraintT<std::greater<Time>>(1)}};
	zones::Zone_slice zone1 = zones::Zone_slice(constraint1, "x", ZONE_INFTY);

	CHECK(zone1.upper_bound_ == ZONE_INFTY);

	std::multimap<std::string, automata::ClockConstraint> constraint2 = { {"x", automata::AtomicClockConstraintT<std::greater<Time>>(1)},
																	{"x", automata::AtomicClockConstraintT<std::less<Time>>(2)}};
	
	//zones::Zone_slice zone2 = zones::Zone_slice(constraint2, "x");

	std::multimap<std::string, automata::ClockConstraint> constraint3 = { {"x", automata::AtomicClockConstraintT<std::equal_to<Time>>(1)},
																	{"x", automata::AtomicClockConstraintT<std::less_equal<Time>>(2)}};

	//zones::Zone_slice zone3 = zones::Zone_slice(constraint3, "x");

	std::multimap<std::string, automata::ClockConstraint> constraint4 = { {"x", automata::AtomicClockConstraintT<std::greater_equal<Time>>(1)}};

	zones::Zone_slice zone4 = zones::Zone_slice(constraint4, "x", ZONE_INFTY);

	search::PlantZoneState<std::string> ta_state1 = {"l0", "x", constraint1, ZONE_INFTY};
	ta_state1.increment_valuation();
	CHECK(ta_state1.symbolic_valuation == zone1);

	search::PlantZoneState<std::string> ta_state2 = {"l0", "x", constraint2, ZONE_INFTY};
	ta_state2.increment_valuation();
	CHECK(ta_state2.symbolic_valuation == zone1);

	search::PlantZoneState<std::string> ta_state3 = {"l0", "x", constraint3, ZONE_INFTY};
	ta_state3.increment_valuation();
	CHECK(ta_state3.symbolic_valuation == zone4);
}

TEST_CASE("Getting Clock Constraints from ATA", "[zones]")
{
	using AlternatingTimedAutomaton = automata::ata::AlternatingTimedAutomaton<std::string, std::string>;
	using ATATransition             = automata::ata::Transition<std::string, std::string>;
	using TrueFormula               = automata::ata::TrueFormula<std::string>;
	using FalseFormula              = automata::ata::FalseFormula<std::string>;
	using LocationFormula           = automata::ata::LocationFormula<std::string>;
	using ClockConstraintFormula    = automata::ata::ClockConstraintFormula<std::string>;
	using ConjunctionFormula        = automata::ata::ConjunctionFormula<std::string>;
	using DisjunctionFormula        = automata::ata::DisjunctionFormula<std::string>;
	using ResetClockFormula         = automata::ata::ResetClockFormula<std::string>;

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
	using TimedAutomaton = automata::ta::TimedAutomaton<std::string, std::string>;
	using Location = automata::ta::Location<std::string>;
	using TATransition   = automata::ta::Transition<std::string, std::string>;
	using CanonicalABZoneWord = search::CanonicalABZoneWord<Location, std::string>;
	using AP = logic::AtomicProposition<std::string>;

	[[maybe_unused]] automata::ClockConstraint c_eq0 = automata::AtomicClockConstraintT<std::equal_to<Time>>(0);

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

	CanonicalABZoneWord initial_word{ta.get_initial_configuration(), ata.get_initial_configuration(), 2};

	zones::Zone_DBM should_be_dbm{std::set<std::string>{}, 2};
	should_be_dbm.add_clock("x");
	should_be_dbm.conjunct("x", c_eq0);
	should_be_dbm.normalize();
	should_be_dbm.add_clock("l0");
	should_be_dbm.conjunct("l0", c_eq0);
	should_be_dbm.normalize();

	CHECK(initial_word.dbm.has_clock("x"));
	CHECK(initial_word.dbm == should_be_dbm);

	CHECK(initial_word.is_valid());

	automata::ta::Location<std::string> ta_location = automata::ta::Location<std::string>{"s0"};
	std::set<std::string> ta_clocks{"x"};
	std::set<logic::MTLFormula<std::string>> ata_locations{logic::MTLFormula<std::string>{AP{"l0"}}};

	CHECK(initial_word.ta_location == ta_location);
	CHECK(initial_word.ta_clocks == ta_clocks);
	CHECK(initial_word.ata_locations == ata_locations);
}

TEST_CASE("monotone_domination_order for zones", "[zones]")
{
	using CanonicalABZoneWord = search::CanonicalABZoneWord<std::string, std::string>;
	using ATALocation = logic::MTLFormula<std::string>;
	using AP = logic::AtomicProposition<std::string>;

	[[maybe_unused]] automata::ClockConstraint c_eq0 = automata::AtomicClockConstraintT<std::equal_to<Time>>(0);
	[[maybe_unused]] automata::ClockConstraint c_ge1 = automata::AtomicClockConstraintT<std::greater_equal<Time>>(1);
	[[maybe_unused]] automata::ClockConstraint c_gt2 = automata::AtomicClockConstraintT<std::greater<Time>>(2);
	[[maybe_unused]] automata::ClockConstraint c_lt3 = automata::AtomicClockConstraintT<std::less<Time>>(3);

	zones::Zone_DBM zone0 = zones::Zone_DBM{ {{"c0", c_eq0}}, 3};
	zones::Zone_DBM zone1 = zones::Zone_DBM{ {{"c0", c_ge1}}, 3};
	zones::Zone_DBM zone2 = zones::Zone_DBM{ {{"c0", c_eq0}, {"c1", c_ge1}}, 3};
	zones::Zone_DBM zone3 = zones::Zone_DBM{ {{"c0", c_eq0}, {"a0", c_gt2}}, 3};
	zones::Zone_DBM zone4 = zones::Zone_DBM{ {{"c0", c_eq0}, {"c1", c_ge1}, {"a0", c_gt2}}, 3};

	CHECK(search::is_monotonically_dominated(
	  CanonicalABZoneWord({"s0"}, {"c0"}, {}, zone0),
	  CanonicalABZoneWord({"s0"}, {"c0"}, {}, zone0)));
	CHECK(!search::is_monotonically_dominated(
	  CanonicalABZoneWord({"s0"}, {"c0"}, {}, zone0),
	  CanonicalABZoneWord({"s0"}, {"c0"}, {}, zone1)));
	CHECK(!search::is_monotonically_dominated(
	  CanonicalABZoneWord({"s0"}, {"c0"}, {ATALocation{AP{"a0"}}}, zone3),
	  CanonicalABZoneWord({"s0"}, {"c0"}, {}, zone0)));
	CHECK(search::is_monotonically_dominated(
	  CanonicalABZoneWord({"s0"}, {"c0", "c1"}, {}, zone2),
	  CanonicalABZoneWord({"s0"}, {"c0", "c1"}, {}, zone2)));
	CHECK(search::is_monotonically_dominated(
	  CanonicalABZoneWord({"s0"}, {"c0"}, {ATALocation{AP{"a0"}}}, zone3),
	  CanonicalABZoneWord({"s0"}, {"c0"}, {ATALocation{AP{"a0"}}}, zone3)));
	CHECK(!search::is_monotonically_dominated(
	  CanonicalABZoneWord({"s0"}, {"c0"}, {ATALocation{AP{"a0"}}}, zone3),
	  CanonicalABZoneWord({"s0"}, {"c0"}, {}, zone0)));
	CHECK(search::is_monotonically_dominated(
	  CanonicalABZoneWord({"s0"}, {"c0"}, {}, zone0),
	  CanonicalABZoneWord({"s0"}, {"c0"}, {ATALocation{AP{"a0"}}}, zone3)));
	CHECK(search::is_monotonically_dominated(
	  CanonicalABZoneWord({"s0"}, {"c0"}, {}, zone0),
	  CanonicalABZoneWord({"s0"}, {"c0", "c1"}, {ATALocation{AP{"a0"}}}, zone4)));
}

TEST_CASE("Difference Bound Matrix tests", "[zones]")
{
	using zones::Zone_DBM;
	using zones::DBM_Entry;

	SECTION("Basic checks") {
		CHECK(!	(DBM_Entry{0, true} < DBM_Entry{-1*((int) 0), false}));
	}

	[[maybe_unused]] automata::ClockConstraint c_eq0 = automata::AtomicClockConstraintT<std::equal_to<Time>>(0);
	[[maybe_unused]] automata::ClockConstraint c_lt1 = automata::AtomicClockConstraintT<std::less<Time>>(1);
	[[maybe_unused]] automata::ClockConstraint c_eq3 = automata::AtomicClockConstraintT<std::equal_to<Time>>(3);
	[[maybe_unused]] automata::ClockConstraint c_ge3 = automata::AtomicClockConstraintT<std::greater_equal<Time>>(3);
	[[maybe_unused]] automata::ClockConstraint c_lt5 = automata::AtomicClockConstraintT<std::less<Time>>(5);
	[[maybe_unused]] automata::ClockConstraint c_le5 = automata::AtomicClockConstraintT<std::less_equal<Time>>(5);
	[[maybe_unused]] automata::ClockConstraint c_gt5 = automata::AtomicClockConstraintT<std::greater<Time>>(5);
	[[maybe_unused]] automata::ClockConstraint c_ge5 = automata::AtomicClockConstraintT<std::greater_equal<Time>>(5);
	[[maybe_unused]] automata::ClockConstraint c_le9 = automata::AtomicClockConstraintT<std::less_equal<Time>>(9);
	[[maybe_unused]] automata::ClockConstraint c_le14 = automata::AtomicClockConstraintT<std::less_equal<Time>>(14);
	[[maybe_unused]] automata::ClockConstraint c_ge15 = automata::AtomicClockConstraintT<std::greater_equal<Time>>(15);

	std::multimap<std::string, automata::ClockConstraint> clock_constraints;

	clock_constraints.insert( {"x", c_ge3} );
	clock_constraints.insert( {"x", c_le9} );
	clock_constraints.insert( {"y", c_eq3} );
	clock_constraints.insert( {"z", c_eq3} );

	std::set<std::string> clocks{"x", "y", "z"};

	Zone_DBM dbm{clocks, 9};

	SECTION("Correct Indexes"){
		CHECK(dbm.size() == 3);

		CHECK(dbm.get_indexes(clocks).at("x") == 1);
		CHECK(dbm.get_indexes(clocks).at("y") == 2);
		CHECK(dbm.get_indexes(clocks).at("z") == 3);
	}

	dbm.conjunct("x", c_ge3);
	dbm.conjunct("x", c_le9);
	dbm.conjunct("y", c_eq3);
	dbm.conjunct("z", c_eq3);

	SECTION("Correct initialization") {

		INFO(dbm);
		
		CHECK(dbm.at(0, 0) == DBM_Entry{0, true});
		CHECK(dbm.at("x", "x") == DBM_Entry{0, true});
		CHECK(dbm.at("y", "y") == DBM_Entry{0, true});
		CHECK(dbm.at("z", "z") == DBM_Entry{0, true});

		CHECK(dbm.at(0, "x") == DBM_Entry{-3, true});
		CHECK(dbm.at(0, "y") == DBM_Entry{-3, true});
		CHECK(dbm.at(0, "z") == DBM_Entry{-3, true});

		CHECK(dbm.at("x", 0) == DBM_Entry{9, true});
		CHECK(dbm.at("y", 0) == DBM_Entry{3, true});
		CHECK(dbm.at("z", 0) == DBM_Entry{3, true});

		CHECK(dbm.at("x", "y") == DBM_Entry{6, true});
		CHECK(dbm.at("y", "x") == DBM_Entry{0, true});

		CHECK(dbm.at("x", "z") == DBM_Entry{6, true});
		CHECK(dbm.at("z", "x") == DBM_Entry{0, true});

		CHECK(dbm.at("y", "z") == DBM_Entry{0, true});
		CHECK(dbm.at("z", "y") == DBM_Entry{0, true});
	}

	dbm.delay();

	SECTION("Correct Delay") {

		INFO(dbm);

		CHECK(dbm.at(0, 0) == DBM_Entry{0, true});
		CHECK(dbm.at("x", "x") == DBM_Entry{0, true});
		CHECK(dbm.at("y", "y") == DBM_Entry{0, true});
		CHECK(dbm.at("z", "z") == DBM_Entry{0, true});

		CHECK(dbm.at(0, "x") == DBM_Entry{-3, true});
		CHECK(dbm.at(0, "y") == DBM_Entry{-3, true});
		CHECK(dbm.at(0, "z") == DBM_Entry{-3, true});

		CHECK(dbm.at("x", 0).infinity_);
		CHECK(dbm.at("y", 0).infinity_);
		CHECK(dbm.at("z", 0).infinity_);

		CHECK(dbm.at("x", "y") == DBM_Entry{6, true});
		CHECK(dbm.at("y", "x") == DBM_Entry{0, true});

		CHECK(dbm.at("x", "z") == DBM_Entry{6, true});
		CHECK(dbm.at("z", "x") == DBM_Entry{0, true});

		CHECK(dbm.at("y", "z") == DBM_Entry{0, true});
		CHECK(dbm.at("z", "y") == DBM_Entry{0, true});
	}

	std::multimap<std::string, automata::ClockConstraint> new_constraints1{ {"x", c_gt5}, {"y", c_gt5} };

	dbm.conjunct(new_constraints1);

	SECTION("Correct new Constraints") {

		INFO(dbm);

		CHECK(dbm.at(0, 0) == DBM_Entry{0, true});
		CHECK(dbm.at("x", "x") == DBM_Entry{0, true});
		CHECK(dbm.at("y", "y") == DBM_Entry{0, true});
		CHECK(dbm.at("z", "z") == DBM_Entry{0, true});

		CHECK(dbm.at(0, "x") == DBM_Entry{-5, false});
		CHECK(dbm.at(0, "y") == DBM_Entry{-5, false});
		CHECK(dbm.at(0, "z") == DBM_Entry{-5, false});

		CHECK(dbm.at("x", 0).infinity_);
		CHECK(dbm.at("y", 0).infinity_);
		CHECK(dbm.at("z", 0).infinity_);

		CHECK(dbm.at("x", "y") == DBM_Entry{6, true});
		CHECK(dbm.at("y", "x") == DBM_Entry{0, true});

		CHECK(dbm.at("x", "z") == DBM_Entry{6, true});
		CHECK(dbm.at("z", "x") == DBM_Entry{0, true});

		CHECK(dbm.at("y", "z") == DBM_Entry{0, true});
		CHECK(dbm.at("z", "y") == DBM_Entry{0, true});
	}

	SECTION("Correct Inconsistency") {
		Zone_DBM new_dbm{{"x"}, 10};

		new_dbm.conjunct("x", c_eq0);

		new_dbm.conjunct("x", c_eq3);

		CHECK(!new_dbm.is_consistent());

		Zone_DBM newer_dbm{{"x"}, 5};

		newer_dbm.conjunct("x", c_gt5);
		newer_dbm.conjunct("x", c_le9);

		INFO(newer_dbm);

		INFO(newer_dbm.get_zone_slice("x"));

		CHECK(newer_dbm.is_consistent());

	}

	SECTION("Checking resulting Zone_slices") {
		CHECK(dbm.get_zone_slice("x") == zones::Zone_slice{5, 9, true, false, 9});
		CHECK(dbm.get_zone_slice("y") == zones::Zone_slice{5, 9, true, false, 9});
		CHECK(dbm.get_zone_slice("z") == zones::Zone_slice{5, 9, true, false, 9});

		Zone_DBM new_dbm{clocks, 5};

		INFO(new_dbm);

		CHECK(new_dbm.get_zone_slice("x") == zones::Zone_slice{0, 5, false, false, 5});
		CHECK(new_dbm.get_zone_slice("y") == zones::Zone_slice{0, 5, false, false, 5});
		CHECK(new_dbm.get_zone_slice("z") == zones::Zone_slice{0, 5, false, false, 5});

		new_dbm.conjunct("x", c_eq0);

		CHECK(new_dbm.get_zone_slice("x") == zones::Zone_slice{0, 0, false, false, 5});
	}

	SECTION("Checking exceeding max constant and normalization") {
		Zone_DBM new_dbm{clocks, 5};

		new_dbm.conjunct("y", c_eq0);
		new_dbm.conjunct("z", c_eq0);

		new_dbm.delay();

		new_dbm.conjunct("y", c_ge15);

		CHECK(new_dbm.at(0, "y") == DBM_Entry{-5, false});
		CHECK(new_dbm.at(0, "z") == DBM_Entry{-5, false});

		new_dbm.conjunct("z", c_le14);

		CHECK(new_dbm.at("y", 0).infinity_);
		CHECK(new_dbm.at("z", 0).infinity_);

		CHECK(new_dbm.get_zone_slice("x") == zones::Zone_slice{0, 5, false, false, 5});
		CHECK(new_dbm.get_zone_slice("y") == zones::Zone_slice{5, 5, true, false, 5});
		CHECK(new_dbm.get_zone_slice("z") == zones::Zone_slice{5, 5, true, false, 5});
	}

	SECTION("Checking Inserting/Removing Clocks") {
		Zone_DBM new_dbm{clocks, 20};

		new_dbm.conjunct("x", c_ge3);
		new_dbm.conjunct("x", c_le14);
		new_dbm.conjunct("y", c_eq0);
		new_dbm.conjunct("z", c_eq0);

		//Sanity check
		CHECK(new_dbm.at(0, 0) == DBM_Entry{0, true});
		CHECK(new_dbm.at("x", "x") == DBM_Entry{0, true});
		CHECK(new_dbm.at("y", "y") == DBM_Entry{0, true});
		CHECK(new_dbm.at("z", "z") == DBM_Entry{0, true});

		CHECK(new_dbm.at(0, "x") == DBM_Entry{-3, true});
		CHECK(new_dbm.at(0, "y") == DBM_Entry{0, true});
		CHECK(new_dbm.at(0, "z") == DBM_Entry{0, true});

		CHECK(new_dbm.at("x", 0) == DBM_Entry{14, true});
		CHECK(new_dbm.at("y", 0) == DBM_Entry{0, true});
		CHECK(new_dbm.at("z", 0) == DBM_Entry{0, true});

		CHECK(new_dbm.at("x", "y") == DBM_Entry{14, true});
		CHECK(new_dbm.at("y", "x") == DBM_Entry{-3, true});

		CHECK(new_dbm.at("x", "z") == DBM_Entry{14, true});
		CHECK(new_dbm.at("z", "x") == DBM_Entry{-3, true});

		CHECK(new_dbm.at("y", "z") == DBM_Entry{0, true});
		CHECK(new_dbm.at("z", "y") == DBM_Entry{0, true});

		//Add new clock
		new_dbm.add_clock("a");
		new_dbm.conjunct("a", c_eq0);

		CHECK(new_dbm.at(0, 0) == DBM_Entry{0, true});
		CHECK(new_dbm.at("x", "x") == DBM_Entry{0, true});
		CHECK(new_dbm.at("y", "y") == DBM_Entry{0, true});
		CHECK(new_dbm.at("z", "z") == DBM_Entry{0, true});
		CHECK(new_dbm.at("a", "a") == DBM_Entry{0, true});

		CHECK(new_dbm.at(0, "x") == DBM_Entry{-3, true});
		CHECK(new_dbm.at(0, "y") == DBM_Entry{0, true});
		CHECK(new_dbm.at(0, "z") == DBM_Entry{0, true});
		CHECK(new_dbm.at(0, "a") == DBM_Entry{0, true});

		CHECK(new_dbm.at("x", 0) == DBM_Entry{14, true});
		CHECK(new_dbm.at("y", 0) == DBM_Entry{0, true});
		CHECK(new_dbm.at("z", 0) == DBM_Entry{0, true});
		CHECK(new_dbm.at("a", 0) == DBM_Entry{0, true});

		CHECK(new_dbm.at("x", "y") == DBM_Entry{14, true});
		CHECK(new_dbm.at("y", "x") == DBM_Entry{-3, true});

		CHECK(new_dbm.at("x", "z") == DBM_Entry{14, true});
		CHECK(new_dbm.at("z", "x") == DBM_Entry{-3, true});

		CHECK(new_dbm.at("x", "a") == DBM_Entry{14, true});
		CHECK(new_dbm.at("a", "x") == DBM_Entry{-3, true});

		CHECK(new_dbm.at("y", "z") == DBM_Entry{0, true});
		CHECK(new_dbm.at("z", "y") == DBM_Entry{0, true});

		CHECK(new_dbm.at("y", "a") == DBM_Entry{0, true});
		CHECK(new_dbm.at("a", "y") == DBM_Entry{0, true});

		CHECK(new_dbm.at("z", "a") == DBM_Entry{0, true});
		CHECK(new_dbm.at("a", "z") == DBM_Entry{0, true});

		new_dbm.delay();

		new_dbm.conjunct("a", c_le9);
		new_dbm.conjunct("x", c_le14);

		CHECK(new_dbm.at(0, 0) == DBM_Entry{0, true});
		CHECK(new_dbm.at("x", "x") == DBM_Entry{0, true});
		CHECK(new_dbm.at("y", "y") == DBM_Entry{0, true});
		CHECK(new_dbm.at("z", "z") == DBM_Entry{0, true});
		CHECK(new_dbm.at("a", "a") == DBM_Entry{0, true});

		CHECK(new_dbm.at(0, "x") == DBM_Entry{-3, true});
		CHECK(new_dbm.at(0, "y") == DBM_Entry{0, true});
		CHECK(new_dbm.at(0, "z") == DBM_Entry{0, true});
		CHECK(new_dbm.at(0, "a") == DBM_Entry{0, true});

		CHECK(new_dbm.at("x", 0) == DBM_Entry{14, true});
		CHECK(new_dbm.at("y", 0) == DBM_Entry{9, true});
		CHECK(new_dbm.at("z", 0) == DBM_Entry{9, true});
		CHECK(new_dbm.at("a", 0) == DBM_Entry{9, true});

		CHECK(new_dbm.at("x", "y") == DBM_Entry{14, true});
		CHECK(new_dbm.at("y", "x") == DBM_Entry{-3, true});

		CHECK(new_dbm.at("x", "z") == DBM_Entry{14, true});
		CHECK(new_dbm.at("z", "x") == DBM_Entry{-3, true});

		CHECK(new_dbm.at("x", "a") == DBM_Entry{14, true});
		CHECK(new_dbm.at("a", "x") == DBM_Entry{-3, true});

		CHECK(new_dbm.at("y", "z") == DBM_Entry{0, true});
		CHECK(new_dbm.at("z", "y") == DBM_Entry{0, true});

		CHECK(new_dbm.at("y", "a") == DBM_Entry{0, true});
		CHECK(new_dbm.at("a", "y") == DBM_Entry{0, true});

		CHECK(new_dbm.at("z", "a") == DBM_Entry{0, true});
		CHECK(new_dbm.at("a", "z") == DBM_Entry{0, true});

		new_dbm.remove_clock("a");

		CHECK(new_dbm.at(0, 0) == DBM_Entry{0, true});
		CHECK(new_dbm.at("x", "x") == DBM_Entry{0, true});
		CHECK(new_dbm.at("y", "y") == DBM_Entry{0, true});
		CHECK(new_dbm.at("z", "z") == DBM_Entry{0, true});

		CHECK(new_dbm.at(0, "x") == DBM_Entry{-3, true});
		CHECK(new_dbm.at(0, "y") == DBM_Entry{0, true});
		CHECK(new_dbm.at(0, "z") == DBM_Entry{0, true});

		CHECK(new_dbm.at("x", 0) == DBM_Entry{14, true});
		CHECK(new_dbm.at("y", 0) == DBM_Entry{9, true});
		CHECK(new_dbm.at("z", 0) == DBM_Entry{9, true});

		CHECK(new_dbm.at("x", "y") == DBM_Entry{14, true});
		CHECK(new_dbm.at("y", "x") == DBM_Entry{-3, true});

		CHECK(new_dbm.at("x", "z") == DBM_Entry{14, true});
		CHECK(new_dbm.at("z", "x") == DBM_Entry{-3, true});

		CHECK(new_dbm.at("y", "z") == DBM_Entry{0, true});
		CHECK(new_dbm.at("z", "y") == DBM_Entry{0, true});

		new_dbm.remove_clock("y");

		new_dbm.reset("x");

		CHECK(new_dbm.at(0, 0) == DBM_Entry{0, true});
		CHECK(new_dbm.at("x", "x") == DBM_Entry{0, true});
		CHECK(new_dbm.at("z", "z") == DBM_Entry{0, true});

		CHECK(new_dbm.at(0, "x") == DBM_Entry{0, true});
		CHECK(new_dbm.at(0, "z") == DBM_Entry{0, true});

		CHECK(new_dbm.at("x", 0) == DBM_Entry{0, true});
		CHECK(new_dbm.at("z", 0) == DBM_Entry{9, true});

		CHECK(new_dbm.at("x", "z") == DBM_Entry{0, true});
		CHECK(new_dbm.at("z", "x") == DBM_Entry{9, true});

		new_dbm.delay();

		CHECK(new_dbm.at(0, 0) == DBM_Entry{0, true});
		CHECK(new_dbm.at("x", "x") == DBM_Entry{0, true});
		CHECK(new_dbm.at("z", "z") == DBM_Entry{0, true});

		CHECK(new_dbm.at(0, "x") == DBM_Entry{0, true});
		CHECK(new_dbm.at(0, "z") == DBM_Entry{0, true});

		CHECK(new_dbm.at("x", 0).infinity_);
		CHECK(new_dbm.at("z", 0).infinity_);

		CHECK(new_dbm.at("x", "z") == DBM_Entry{0, true});
		CHECK(new_dbm.at("z", "x") == DBM_Entry{9, true});

		new_dbm.copy_clock("y", "z");

		CHECK(new_dbm.at(0, 0) == DBM_Entry{0, true});
		CHECK(new_dbm.at("x", "x") == DBM_Entry{0, true});
		CHECK(new_dbm.at("y", "y") == DBM_Entry{0, true});
		CHECK(new_dbm.at("z", "z") == DBM_Entry{0, true});

		CHECK(new_dbm.at(0, "x") == DBM_Entry{0, true});
		CHECK(new_dbm.at(0, "y") == DBM_Entry{0, true});
		CHECK(new_dbm.at(0, "z") == DBM_Entry{0, true});

		CHECK(new_dbm.at("x", 0).infinity_);
		CHECK(new_dbm.at("y", 0).infinity_);
		CHECK(new_dbm.at("z", 0).infinity_);

		CHECK(new_dbm.at("x", "y") == DBM_Entry{0, true});
		CHECK(new_dbm.at("y", "x") == DBM_Entry{9, true});

		CHECK(new_dbm.at("x", "z") == DBM_Entry{0, true});
		CHECK(new_dbm.at("z", "x") == DBM_Entry{9, true});

		CHECK(new_dbm.at("y", "z") == DBM_Entry{0, true});
		CHECK(new_dbm.at("z", "y") == DBM_Entry{0, true});
	}

	SECTION("Correct Normalization") {
		Zone_DBM new_dbm{clocks, 4};

		new_dbm.conjunct("x", c_ge15);
		new_dbm.conjunct("y", c_le9);
		new_dbm.conjunct("z", c_eq3);

		new_dbm.normalize();

		CHECK(new_dbm.at(0, "x") == DBM_Entry{-4, false});
		CHECK(new_dbm.at("y", 0).infinity_);
		CHECK(new_dbm.at(0, "z") == DBM_Entry{-3, true});
		CHECK(new_dbm.at("z", 0) == DBM_Entry{3, true});

		new_dbm.reset("x");
		new_dbm.delay();
		new_dbm.conjunct("x", c_ge15);

		new_dbm.normalize();

		INFO(new_dbm);

		CHECK((!dbm.at(0, "z").infinity_ && dbm.at(0, "z") < DBM_Entry{-1*((int) 4), false}));

		CHECK(new_dbm.at(0, "x") == DBM_Entry{-4, false});
		CHECK(new_dbm.at("y", 0).infinity_);
		CHECK(new_dbm.at(0, "z") == DBM_Entry{-4, false});
		CHECK(new_dbm.at("z", 0).infinity_);
	}

	SECTION("More edge cases") {
		Zone_DBM new_dbm{clocks, 5};

		new_dbm.conjunct("x", c_eq0);
		new_dbm.conjunct("y", c_eq0);
		new_dbm.conjunct("z", c_eq0);
		new_dbm.delay();

		new_dbm.conjunct("x", c_ge3);
		new_dbm.reset("x");
		new_dbm.delay();
		
		new_dbm.conjunct("x", c_ge3);
		new_dbm.reset("x");

		INFO(new_dbm.get_zone_slice("y"));

		std::vector<automata::ClockConstraint> constraints = zones::get_clock_constraints_from_zone(new_dbm.get_zone_slice("y"), 5);
		for(const auto &constraint : constraints) {
			new_dbm.conjunct("y", constraint);
		}

		INFO(*constraints.begin());

		INFO(new_dbm);

		CHECK(new_dbm.is_consistent());
	}

	SECTION("Testing Getting a Subset") {
		Zone_DBM new_dbm{clocks, 5};

		new_dbm.conjunct("x", c_lt1);
		new_dbm.conjunct("y", c_eq3);
		new_dbm.conjunct("z", c_eq3);

		Zone_DBM small_dbm = new_dbm.get_subset({"x", "y"});
		Zone_DBM should_be_dbm{std::set<std::string>{"x", "y"}, 5};

		should_be_dbm.conjunct("x", c_lt1);
		should_be_dbm.conjunct("y", c_eq3);

		CHECK(small_dbm == should_be_dbm);

		//Make sure there are no side effects
		small_dbm.delay();
		CHECK(!new_dbm.at("x", 0).infinity_);
		CHECK(!new_dbm.at("y", 0).infinity_);
	}
}

TEST_CASE("Manually Debugging Railway example", "[zones]") {
	using CanonicalABZoneWord = search::CanonicalABZoneWord<std::string, std::string>;
	using zones::Zone_DBM;
	using zones::DBM_Entry;

	//A bunch of constraints for easy access
	[[maybe_unused]] automata::ClockConstraint c_eq0 = automata::AtomicClockConstraintT<std::equal_to<Time>>(0);
	[[maybe_unused]] automata::ClockConstraint c_ge0 = automata::AtomicClockConstraintT<std::greater_equal<Time>>(0);
	[[maybe_unused]] automata::ClockConstraint c_le1 = automata::AtomicClockConstraintT<std::less_equal<Time>>(1);
	[[maybe_unused]] automata::ClockConstraint c_lt1 = automata::AtomicClockConstraintT<std::less<Time>>(1);
	[[maybe_unused]] automata::ClockConstraint c_eq1 = automata::AtomicClockConstraintT<std::equal_to<Time>>(1);
	[[maybe_unused]] automata::ClockConstraint c_eq2 = automata::AtomicClockConstraintT<std::equal_to<Time>>(2);
	[[maybe_unused]] automata::ClockConstraint c_gt2 = automata::AtomicClockConstraintT<std::greater<Time>>(2);
	[[maybe_unused]] automata::ClockConstraint c_eq3 = automata::AtomicClockConstraintT<std::equal_to<Time>>(3);
	[[maybe_unused]] automata::ClockConstraint c_ge3 = automata::AtomicClockConstraintT<std::greater_equal<Time>>(3);
	[[maybe_unused]] automata::ClockConstraint c_lt5 = automata::AtomicClockConstraintT<std::less<Time>>(5);
	[[maybe_unused]] automata::ClockConstraint c_le5 = automata::AtomicClockConstraintT<std::less_equal<Time>>(5);
	[[maybe_unused]] automata::ClockConstraint c_gt5 = automata::AtomicClockConstraintT<std::greater<Time>>(5);
	[[maybe_unused]] automata::ClockConstraint c_ge5 = automata::AtomicClockConstraintT<std::greater_equal<Time>>(5);
	[[maybe_unused]] automata::ClockConstraint c_le9 = automata::AtomicClockConstraintT<std::less_equal<Time>>(9);
	[[maybe_unused]] automata::ClockConstraint c_le14 = automata::AtomicClockConstraintT<std::less_equal<Time>>(14);
	[[maybe_unused]] automata::ClockConstraint c_ge15 = automata::AtomicClockConstraintT<std::greater_equal<Time>>(15);

	SECTION("Combining node's canonical words") {
		Zone_DBM dbm1{std::set<std::string>{"t", "c_1"}, 2, true};
		dbm1.delay();
		dbm1.conjunct("t", c_eq1);

		CHECK(dbm1.at(0, "c_1") == DBM_Entry{-1, true});

		Zone_DBM dbm2 = dbm1;

		dbm1.add_clock("l0");
		dbm1.conjunct("t", c_eq1);

		dbm2.add_clock("l1");
		dbm2.conjunct("l1", c_lt1);

		logic::MTLFormula<std::string> l0{logic::AtomicProposition<std::string>{"l0"}};
		logic::MTLFormula<std::string> l1{logic::AtomicProposition<std::string>{"l1"}};

		CanonicalABZoneWord word1{"s0", {"c_1", "t"}, {l0}, dbm1};
		CanonicalABZoneWord word2{"s0", {"c_1", "t"}, {l1}, dbm2};

		CHECK(word1 != word2);

		CHECK(reg_a(word1) == reg_a(word2));

		std::map<std::pair<RegionIndex, std::string>,
				std::set<CanonicalABZoneWord>>
		successors = {
			{{2, "leave"}, {word1}},
			{{4, "leave"}, {word2}}
		};

		CHECK(successors.at({2, "leave"}) == std::set<CanonicalABZoneWord>{word1});
		CHECK(successors.at({4, "leave"}) == std::set<CanonicalABZoneWord>{word2});

		//If two child classes for the same action (but different time increment) share the same
		//Plant part, then they can share the same canonical words too.
		for(auto &[key1, set1] : successors) {
			for(auto &[key2, set2] : successors) {
				if(key1 == key2) {
					continue;
				}

				if(key1.second == key2.second && reg_a(*set1.begin()) == reg_a(*set2.begin())) {
					set1.insert(set2.begin(), set2.end());
				}
			}
		}

		CHECK(successors.at({2, "leave"}) == std::set<CanonicalABZoneWord>{word1, word2});
		CHECK(successors.at({4, "leave"}) == std::set<CanonicalABZoneWord>{word1, word2});
	}
}

TEST_CASE("Simple example using zones 1", "[zones]")
{
	using TimedAutomaton = automata::ta::TimedAutomaton<std::string, std::string>;
	using Location = automata::ta::Location<std::string>;
	using TATransition   = automata::ta::Transition<std::string, std::string>;
	using CanonicalABZoneWord = search::CanonicalABZoneWord<Location, std::string>;
	using TreeSearch =
		search::ZoneTreeSearch<Location, std::string>;

	[[maybe_unused]] automata::ClockConstraint c_eq0 = automata::AtomicClockConstraintT<std::equal_to<Time>>(0);
	[[maybe_unused]] automata::ClockConstraint c_eq2 = automata::AtomicClockConstraintT<std::equal_to<Time>>(2);

	TimedAutomaton ta{{Location{"s0"}, Location{"s1"}, Location{"s2"}, Location{"bad"}, Location{"good"}, Location{"great"}, Location{"amazing"}},
		  {"transit", "c1", "c2", "c3", "e1", "e2", "e3"},
		  Location{"s0"},
		  {Location{"s0"}, Location{"bad"}, Location{"amazing"}},
		  {"x", "y"},
		  {TATransition(Location{"s0"}, "transit", Location{"s1"}, {{"x", automata::AtomicClockConstraintT<std::equal_to<Time>>(2)}}, {"x"}),
		   TATransition(Location{"s1"}, "transit", Location{"s2"}, {{"x", automata::AtomicClockConstraintT<std::equal_to<Time>>(2)}}, {"x"}),
		   TATransition(Location{"s2"},
						"c1",
						Location{"good"}),
		   TATransition(Location{"good"},
						"c2",
						Location{"great"}),
			TATransition(Location{"great"},
						"c3",
						Location{"amazing"}),
		   TATransition(Location{"s2"},
						"e1",
						Location{"bad"}, {{"x", automata::AtomicClockConstraintT<std::equal_to<Time>>(2)}}, {"x"}),
			TATransition(Location{"good"},
						"e2",
						Location{"bad"}, {{"x", automata::AtomicClockConstraintT<std::equal_to<Time>>(2)}}, {"x"}),
			TATransition(Location{"great"},
						"e3",
						Location{"bad"}, {{"x", automata::AtomicClockConstraintT<std::equal_to<Time>>(2)}}, {"x"})}};
	
	logic::AtomicProposition<std::string> c1_AP{"c1"};
	logic::AtomicProposition<std::string> c2_AP{"c2"};
	logic::AtomicProposition<std::string> c3_AP{"c3"};
	logic::AtomicProposition<std::string> e1_AP{"e1"};
	logic::AtomicProposition<std::string> e2_AP{"e2"};
	logic::AtomicProposition<std::string> e3_AP{"e3"};
	logic::AtomicProposition<std::string> transit_AP{"transit"};

	logic::MTLFormula c1{c1_AP};
	logic::MTLFormula c2{c2_AP};
	logic::MTLFormula c3{c3_AP};
	logic::MTLFormula e1{e1_AP};
	logic::MTLFormula e2{e2_AP};
	logic::MTLFormula e3{e3_AP};

	logic::MTLFormula phi1 = e1.dual_until(!c1) || e2.dual_until(!c2) || e3.dual_until(!c3);		

	auto ata = mtl_ata_translation::translate(phi1, {e1_AP, e2_AP, e3_AP, c1_AP, c2_AP, c3_AP, transit_AP});

	//CAPTURE(ata);

	visualization::ta_to_graphviz(ta)
	  .render_to_file(fmt::format("simple_zone_ta.pdf"));

	std::set<std::string> controller_actions = {"c1", "c2", "c3"};
	std::set<std::string> environment_actions = {"e1", "e2", "e3", "transit"};

	TreeSearch search{&ta,
					  &ata,
					  controller_actions,
					  environment_actions,
					  2,
					  true,
					  true};

	CanonicalABZoneWord initial_word = CanonicalABZoneWord(ta.get_initial_configuration(),
			                        ata.get_initial_configuration(),
			                        2);

	CHECK(!initial_word.ta_clocks.empty());

	CHECK(*search.get_root()->words.begin() == initial_word);

	std::map<std::pair<tacos::RegionIndex, std::string>, std::set<CanonicalABZoneWord>> successors = 
		search.compute_next_canonical_words(initial_word);

	for(const auto &[timed_action, words] : successors) {
		CHECK(!words.empty());
		for(const auto &word : words) {
			INFO(word);
			CHECK(word.is_valid());
			CHECK(ta.get_clocks() == word.ta_clocks);
			//There are no transitions from s0 to s0
			CHECK(word.ta_location != Location{"s0"});
		}
	}

	search.build_tree(true);
	
	CHECK(search.get_root()->label == search::NodeLabel::TOP);
	
	auto controller = controller_synthesis::create_controller(
						search.get_root(), controller_actions, environment_actions, 2
						);
	//CHECK(search::verify_ta_controller(ta, controller, phi1, 2));
	
	#if USE_INTERACTIVE_VISUALIZATION
		char              tmp_filename[] = "search_graph_XXXXXX.svg";
		mkstemps(tmp_filename, 4);
		std::filesystem::path tmp_file(tmp_filename);
		visualization::search_tree_to_graphviz_interactive(search.get_root(), tmp_filename);
	#else
		visualization::search_tree_to_graphviz(*search.get_root(), false)
		  .render_to_file(fmt::format("simple_zone_test.svg"));
	#endif
	visualization::ta_to_graphviz(controller, false)
	  .render_to_file(fmt::format("simple_zone_controller.pdf"));
}

TEST_CASE("Simple example using zones 2", "[zones]")
{
	using TimedAutomaton = automata::ta::TimedAutomaton<std::string, std::string>;
	using Location = automata::ta::Location<std::string>;
	using TATransition   = automata::ta::Transition<std::string, std::string>;
	using CanonicalABZoneWord = search::CanonicalABZoneWord<Location, std::string>;
	using MTLFormula = logic::MTLFormula<std::string>;
	using TreeSearch =
		search::ZoneTreeSearch<Location, std::string>;

	[[maybe_unused]] automata::ClockConstraint c_eq0 = automata::AtomicClockConstraintT<std::equal_to<Time>>(0);
	[[maybe_unused]] automata::ClockConstraint c_ge0 = automata::AtomicClockConstraintT<std::greater_equal<Time>>(0);
	[[maybe_unused]] automata::ClockConstraint c_le1 = automata::AtomicClockConstraintT<std::less_equal<Time>>(1);
	[[maybe_unused]] automata::ClockConstraint c_eq1 = automata::AtomicClockConstraintT<std::equal_to<Time>>(1);
	[[maybe_unused]] automata::ClockConstraint c_ge1 = automata::AtomicClockConstraintT<std::greater_equal<Time>>(1);
	[[maybe_unused]] automata::ClockConstraint c_eq2 = automata::AtomicClockConstraintT<std::equal_to<Time>>(2);

	TimedAutomaton ta{{Location{"OPEN_F"}, Location{"CLOSING_F"}, Location{"CLOSED_F"}, Location{"CLOSED_N"}, Location{"CLOSED_I"}, Location{"CLOSED_B"}, Location{"OPENING_B"}, Location{"OPEN_B"}},
			{"start_c", "finish_c", "get_near", "enter", "leave", "start_o", "finish_o"},
			Location{"OPEN_F"},
			{Location{"OPEN_B"}},
			{"t", "c"},
			{
				TATransition(Location{"OPEN_F"},
							"start_c",
							Location{"CLOSING_F"}, {}, {"c"}),
				TATransition(Location{"CLOSING_F"},
							"finish_c",
							Location{"CLOSED_F"}, {{"c", c_eq1}}, {"c"}),
				TATransition(Location{"CLOSED_F"},
							"get_near",
							Location{"CLOSED_N"}, {{"t", c_eq2}}, {"t"}),
				TATransition(Location{"CLOSED_N"},
							"enter",
							Location{"CLOSED_I"}, {{"t", c_le1}, {"t", c_ge0}}, {"t"}),
				TATransition(Location{"CLOSED_I"},
							"leave",
							Location{"CLOSED_B"}, {{"t", c_eq1}}, {"t"}),
				TATransition(Location{"CLOSED_B"},
							"start_o",
							Location{"OPENING_B"}),
				TATransition(Location{"OPENING_B"},
							"finish_o",
							Location{"OPEN_B"})
			}};
	
	logic::AtomicProposition<std::string> c1_AP{"start_c"};
	logic::AtomicProposition<std::string> c2_AP{"finish_c"};
	logic::AtomicProposition<std::string> e1_AP{"get_near"};
	logic::AtomicProposition<std::string> e2_AP{"enter"};
	logic::AtomicProposition<std::string> e3_AP{"leave"};
	logic::AtomicProposition<std::string> c3_AP{"start_o"};
	logic::AtomicProposition<std::string> c4_AP{"finish_o"};

	MTLFormula c1{c1_AP};
	MTLFormula c2{c2_AP};
	MTLFormula e1{e1_AP};
	MTLFormula e2{e2_AP};
	MTLFormula e3{e3_AP};
	MTLFormula c3{c3_AP};
	MTLFormula c4{c4_AP};

	MTLFormula bottom = !MTLFormula::TRUE();
	MTLFormula phi1 = e2.dual_until(!c2);
	MTLFormula phi2 = c3.dual_until(!e3);
	MTLFormula phi3 = bottom.dual_until(!c4);
	MTLFormula spec = phi1 || phi2 || phi3;


	auto ata = mtl_ata_translation::translate(spec, {c1_AP, c2_AP, c3_AP, c4_AP, e1_AP, e2_AP, e3_AP});
	//CAPTURE(ata);

	visualization::ta_to_graphviz(ta)
	  .render_to_file(fmt::format("simple_ta.pdf"));
	
	std::set<std::string> controller_actions = {"start_c", "finish_c", "start_o", "finish_o"};
	std::set<std::string> environment_actions = {"get_near", "enter", "leave"};

	TreeSearch search{&ta,
					  &ata,
					  controller_actions,
					  environment_actions,
					  2,
					  true, //similar if false, every bad node is still "bad" despite not being so, everything else is just unknown
					  false, //exact same if true
					  };

	SECTION("Test the word where successors are split up") {
		using zones::Zone_DBM;
		using search::ata_formula_to_string;

		auto sink_state = ata.get_sink_location().value();

		Zone_DBM ta_dbm{std::set<std::string>{"t", "c"}, 2};

		ta_dbm.conjunct("c", c_eq1);
		ta_dbm.conjunct("t", c_eq0);

		Zone_DBM dbm1 = ta_dbm;
		dbm1.add_clock(ata_formula_to_string(phi2));
		dbm1.conjunct(ata_formula_to_string(phi2), c_eq2);

		Zone_DBM dbm2 = ta_dbm;
		dbm2.add_clock(ata_formula_to_string(phi3));
		dbm2.conjunct(ata_formula_to_string(phi3), c_eq2);

		Zone_DBM dbm3 = ta_dbm;
		dbm3.add_clock(ata_formula_to_string(sink_state));
		dbm3.conjunct(ata_formula_to_string(sink_state), c_eq0);

		CanonicalABZoneWord word1{Location{"CLOSED_I"}, {"t", "c"}, {phi2}, dbm1};
		CanonicalABZoneWord word2{Location{"CLOSED_I"}, {"t", "c"}, {phi3}, dbm2};
		CanonicalABZoneWord word3{Location{"CLOSED_I"}, {"t", "c"}, {sink_state}, dbm3};

		INFO(word1);
		INFO(word2);
		INFO(word3);

		auto word1_successors = search.compute_next_canonical_words(word1);
		auto word2_successors = search.compute_next_canonical_words(word2);
		auto sink_successors = search.compute_next_canonical_words(word3);

		CanonicalABZoneWord word1_succ = *word1_successors.at({2, "leave"}).begin();
		CanonicalABZoneWord word2_succ = *word2_successors.at({3, "leave"}).begin();
		CanonicalABZoneWord sink_succ = *sink_successors.at({2, "leave"}).begin();

		CHECK(word1_succ == sink_succ);
		CHECK(reg_a(word1_succ) == reg_a(word2_succ));

		word1_successors.insert(word2_successors.begin(), word2_successors.end());
		word2_successors.insert(word1_successors.begin(), word1_successors.end());

		CHECK(word1_successors == word2_successors);

		std::map<std::pair<RegionIndex, std::string>,
				 std::set<CanonicalABZoneWord>>
			child_classes;

		for(const auto &word : {word1, word2, word3}) {
			std::map<std::pair<RegionIndex, std::string>,
						std::set<CanonicalABZoneWord>>
				successors = search.compute_next_canonical_words(word);

			//If this action and increment hasn't been taken yet, just insert it normally
			//Otherwise insert the new canonical words into the set that is found at this key
			for(const auto &[key, set] : successors) {
				if(!child_classes.insert({key, set}).second) {
					child_classes.at(key).insert(set.begin(), set.end());
				}
			}
		}

		//If two child classes for the same action (but different time increment) share the same
		//Plant part, then they can share the same canonical words too, since they just got split up due
		//to different timings for the ATA
		for(auto &[key1, set1] : child_classes) {
			for(auto &[key2, set2] : child_classes) {
				if(key1 == key2) {
					continue;
				}

				//As there is only one transition, all the reg_a will always be the same
				CHECK((key1.second == key2.second && reg_a(*set1.begin()) == reg_a(*set2.begin())));

				if(key1.second == key2.second && reg_a(*set1.begin()) == reg_a(*set2.begin())) {
					set1.insert(set2.begin(), set2.end());
					set2.insert(set1.begin(), set1.end());

					CHECK(set1 == set2);
				}
			}
		}

		for(const auto &[_, succ1] : child_classes) {
			for(const auto &[_, succ2] : child_classes) {
				CHECK(succ1 == succ2);
			}
		}

		std::map<std::pair<RegionIndex, std::string>,
						std::set<CanonicalABZoneWord>>
			should_be_classes = {
				{{2, "leave"}, {word1_succ, word2_succ}},
				{{3, "leave"}, {word1_succ, word2_succ}}
			};

		CHECK(child_classes.size() == 2);
		
		CHECK(child_classes == should_be_classes);
	}


	search.build_tree(true);

	CHECK(search.get_root()->label == search::NodeLabel::TOP);

	if(search.get_root()->label == search::NodeLabel::TOP) {
		auto controller = controller_synthesis::create_controller(
						search.get_root(), controller_actions, environment_actions, 2
						);
		
		visualization::ta_to_graphviz(controller,
									  false)
			.render_to_file(fmt::format("simple_controller.pdf"));
	}
	
	//CHECK(search::verify_ta_controller(plant, controller, spec, K));

	#if USE_INTERACTIVE_VISUALIZATION
		char              tmp_filename[] = "search_graph_XXXXXX.svg";
		mkstemps(tmp_filename, 4);
		std::filesystem::path tmp_file(tmp_filename);
		visualization::search_tree_to_graphviz_interactive(search.get_root(), tmp_filename);
	#else
		visualization::search_tree_to_graphviz(*search.get_root(), false)
		  .render_to_file(fmt::format("simple_example.svg"));
	#endif
}

#if true
TEST_CASE("Railroad example using zones", "[zones]")
{
	using AP = logic::AtomicProposition<std::string>;
	using TreeSearch =
		search::ZoneTreeSearch<automata::ta::Location<std::vector<std::string>>, std::string>;

	//~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~START~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~//

	const auto &[plant, spec, controller_actions, environment_actions] = create_crossing_problem({2});
	[[maybe_unused]] const int num_crossings = 2;
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

	CHECK(K == 2);

	TreeSearch search{&plant,
					  &ata,
					  controller_actions,
					  environment_actions,
					  K,
					  true,
					  true};
	
	search.build_tree(true);
	CHECK(search.get_root()->label == search::NodeLabel::TOP);

	if(search.get_root()->label == search::NodeLabel::TOP) {
		auto controller = controller_synthesis::create_controller(
						search.get_root(), controller_actions, environment_actions, 2
						);
		
		visualization::ta_to_graphviz(controller,
									  false)
			.render_to_file(fmt::format("railroad{}_controller.pdf", num_crossings));
	}
	
	//CHECK(search::verify_ta_controller(plant, controller, spec, K));

	#if USE_INTERACTIVE_VISUALIZATION
		char              tmp_filename[] = "search_graph_XXXXXX.svg";
		mkstemps(tmp_filename, 4);
		std::filesystem::path tmp_file(tmp_filename);
		visualization::search_tree_to_graphviz_interactive(search.get_root(), tmp_filename);
	#else
		visualization::search_tree_to_graphviz(*search.get_root(), true)
		  .render_to_file(fmt::format("railroad{}.svg", num_crossings));
	#endif
}
#endif

} // namespace