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
using TreeSearch =
  search::TreeSearch<automata::ta::Location<std::vector<std::string>>, std::string>;

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
	using CanonicalABZoneWord = search::CanonicalABZoneWord<automata::ta::Location<std::string>, std::string>;

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

	std::set<std::string> clocks{"t", "c_1"};

	Zone_DBM dbm{{"t", "c_1", "l0"}, 2};

	dbm.conjunct("t", c_eq0);
	dbm.conjunct("c_1", c_eq0);
	dbm.conjunct("l0", c_eq0);

	dbm.delay();

	std::multimap<std::string, automata::ClockConstraint> clock_constraints1{ {"t", c_eq2} };
	for(const auto &clock : clocks) {
		auto [curr_constraint, last_constraint] = clock_constraints1.equal_range(clock);
		for(; curr_constraint != last_constraint; curr_constraint++) {
			dbm.conjunct(clock, curr_constraint->second);
		}
	}

	dbm.reset("t");
	dbm.normalize();

	dbm.copy_clock("enter", "l0");
	dbm.copy_clock("start", "l0");
	dbm.copy_clock("travel", "l0");

	std::vector<automata::ClockConstraint> new_constraints1{zones::get_clock_constraints_from_zone(dbm.get_zone_slice("l0"), 2)};

	for(const auto &constraint : new_constraints1) {
		dbm.conjunct("enter", constraint);
	}
	for(const auto &constraint : new_constraints1) {
		dbm.conjunct("start", constraint);
	}
	for(const auto &constraint : new_constraints1) {
		dbm.conjunct("travel", constraint);
	}

	std::multimap<std::string, automata::ClockConstraint> clock_constraints2{ {"t", c_ge0}, {"t", c_le1} };
	for(const auto &clock : clocks) {
		auto [curr_constraint, last_constraint] = clock_constraints2.equal_range(clock);
		for(; curr_constraint != last_constraint; curr_constraint++) {
			dbm.conjunct(clock, curr_constraint->second);
		}
	}
	dbm.reset("t");
	dbm.normalize();

	dbm.copy_clock("start", "start");
	dbm.copy_clock("travel", "travel");

	std::vector<automata::ClockConstraint> new_constraints2_1{zones::get_clock_constraints_from_zone(dbm.get_zone_slice("start"), 2)};
	std::vector<automata::ClockConstraint> new_constraints2_2{zones::get_clock_constraints_from_zone(dbm.get_zone_slice("travel"), 2)};

	for(const auto &constraint : new_constraints2_1) {
		dbm.conjunct("start", constraint);
	}
	for(const auto &constraint : new_constraints2_2) {
		dbm.conjunct("travel", constraint);
	}

	dbm.delay();

	std::multimap<std::string, automata::ClockConstraint> clock_constraints3{ {"t", c_eq1} };
	for(const auto &clock : clocks) {
		auto [curr_constraint, last_constraint] = clock_constraints3.equal_range(clock);
		for(; curr_constraint != last_constraint; curr_constraint++) {
			dbm.conjunct(clock, curr_constraint->second);
		}
	}

	dbm.reset("t");
	dbm.normalize();

	dbm.copy_clock("travel", "travel");

	dbm.add_clock("sink");
	dbm.reset("sink");

	std::vector<automata::ClockConstraint> new_constraints3{zones::get_clock_constraints_from_zone(dbm.get_zone_slice("travel"), 2)};

	for(const auto &constraint : new_constraints3) {
		dbm.conjunct("travel", constraint);
	}

	INFO(dbm);

	dbm.delay();

	std::multimap<std::string, automata::ClockConstraint> clock_constraints4{ {"t", c_eq2} };
	for(const auto &clock : clocks) {
		auto [curr_constraint, last_constraint] = clock_constraints4.equal_range(clock);
		for(; curr_constraint != last_constraint; curr_constraint++) {
			dbm.conjunct(clock, curr_constraint->second);
		}
	}

	dbm.reset("t");
	dbm.normalize();
}

TEST_CASE("Simple example using zones 1", "[zones]")
{
	using TreeSearch =
		search::TreeSearch<automata::ta::Location<std::string>, std::string>;
	using Location = automata::ta::Location<std::string>;
	using CanonicalABZoneWord = search::CanonicalABZoneWord<Location, std::string>;

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
					  true,
					  generate_heuristic<TreeSearch::Node>(),
					  true};

	CanonicalABZoneWord initial_word = CanonicalABZoneWord(ta.get_initial_configuration(),
			                        ata.get_initial_configuration(),
			                        2);

	CHECK(!initial_word.ta_clocks.empty());

	//bug where two sink states lead to third canonical word being ignored
	SECTION("Weird Bug where member of set is ignored") {
		logic::MTLFormula<std::string> ata_location1 = e2.dual_until(!c2);
		logic::MTLFormula<std::string> ata_location2 = e3.dual_until(!c3);
		logic::MTLFormula<std::string> ata_location3 = ata.get_sink_location().value();
		
		zones::Zone_DBM dbm1{{"x", "y", search::ata_formula_to_string(ata_location1)}, 2};
		dbm1.conjunct("x", c_eq0);
		dbm1.conjunct("y", c_eq0);
		dbm1.conjunct(search::ata_formula_to_string(ata_location1), c_eq0);
		dbm1.delay();
		dbm1.conjunct("x", c_eq2);
		dbm1.reset("x");
		dbm1.delay();
		dbm1.conjunct("x", c_eq2);
		dbm1.reset("x");

		zones::Zone_DBM dbm2{{"x", "y", search::ata_formula_to_string(ata_location2)}, 2};
		dbm2.conjunct("x", c_eq0);
		dbm2.conjunct("y", c_eq0);
		dbm2.conjunct(search::ata_formula_to_string(ata_location2), c_eq0);
		dbm2.delay();
		dbm2.conjunct("x", c_eq2);
		dbm2.reset("x");
		dbm2.delay();
		dbm2.conjunct("x", c_eq2);
		dbm2.reset("x");

		zones::Zone_DBM dbm3{{"x", "y", search::ata_formula_to_string(ata_location3)}, 2};
		dbm3.conjunct("x", c_eq0);
		dbm3.conjunct("y", c_eq0);
		dbm3.conjunct(search::ata_formula_to_string(ata_location3), c_eq0);
		dbm3.delay();
		dbm3.conjunct("x", c_eq2);
		dbm3.reset("x");
		dbm3.delay();
		dbm3.conjunct("x", c_eq2);
		dbm3.reset("x");

		CHECK(dbm1.get_zone_slice("x") == zones::Zone_slice{0, 0, false, false, 2});
		CHECK(dbm1.get_zone_slice("y") == zones::Zone_slice{2, 2, true, false, 2});
		CHECK(dbm1.get_zone_slice(search::ata_formula_to_string(ata_location1)) == zones::Zone_slice{2, 2, true, false, 2});

		CanonicalABZoneWord word1{Location{"good"}, {"x", "y"}, {ata_location1}, dbm1};
		CanonicalABZoneWord word2{Location{"good"}, {"x", "y"}, {ata_location2}, dbm2};
		CanonicalABZoneWord word3{Location{"good"}, {"x", "y"}, {ata_location3}, dbm3};

		std::set<CanonicalABZoneWord> words{word1, word2, word3};

		std::map<std::pair<tacos::RegionIndex, std::string>, std::set<CanonicalABZoneWord>> all_successors;

		for(const auto &curr_word : words) {
			std::map<std::pair<tacos::RegionIndex, std::string>, std::set<CanonicalABZoneWord>> successors = 
				search.compute_next_canonical_words(curr_word);
			CHECK(!successors.empty());
			for(const auto &[key, set] : successors) {
				if(!all_successors.insert({key, set}).second) {
					all_successors.at(key).insert(set.begin(), set.end());
				}
			}

			std::set<CanonicalABZoneWord> succ = successors.at(std::make_pair<tacos::RegionIndex, std::string>(0, "c2"));
			INFO(succ);
			//bool satisfiable = !std::all_of(std::begin(succ), std::end(succ), [](const auto &word) {
			//		return std::find_if(std::begin(word.ata_locations), std::end(word.ata_locations), [](const auto &location) {
			//			return location == 
			//				logic::MTLFormula<std::string>{mtl_ata_translation::get_sink<std::string>()};
			//		}) != std::end(word.ata_locations);
			//	});
			CHECK(1 != 1);
		}

		std::set<CanonicalABZoneWord> succ = all_successors.at(std::make_pair<tacos::RegionIndex, std::string>(0, "c2"));
		INFO(succ);
		CHECK(succ.size() == 3);
		bool satisfiable = !std::all_of(std::begin(succ), std::end(succ), [](const auto &word) {
				return std::find_if(std::begin(word.ata_locations), std::end(word.ata_locations), [](const auto &location) {
					return location == 
						logic::MTLFormula<std::string>{mtl_ata_translation::get_sink<std::string>()};
				}) != std::end(word.ata_locations);
			});
		CHECK(satisfiable);
	}

	CHECK(*search.get_root()->zone_words.begin() == initial_word);

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
	CHECK(search::verify_ta_controller(ta, controller, phi1, 2));
	
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
	using TreeSearch =
  search::TreeSearch<automata::ta::Location<std::string>, std::string>;

	//Problem with this: Once "☐¬a" has been reached, a node is labelled bad and search terminates there (even without early termination).
	//However, the action "a" can always still be taken, which would make the ATA go to a sink
	//As such, a "bad" node can actually still lead to a "good" node
	TimedAutomaton ta{{Location{"s0"}, Location{"s1"}, Location{"s2"}},
		  {"a", "b", "c", "d"},
		  Location{"s0"},
		  {Location{"s0"}, Location{"s1"}, Location{"s2"}},
		  {"x"},
		  {TATransition(Location{"s0"},
						"a",
						Location{"s1"}),
		   TATransition(Location{"s0"},
						"b",
						Location{"s2"}),
		   TATransition(Location{"s1"}, "a", Location{"s1"}),
		   TATransition(Location{"s1"}, "c", Location{"s1"}, {{"x", automata::AtomicClockConstraintT<std::equal_to<Time>>(1)}}, {"x"}),
		   TATransition(Location{"s1"}, "d", Location{"s1"}, {{"x", automata::AtomicClockConstraintT<std::equal_to<Time>>(1)}}, {"x"}),
		   TATransition(Location{"s2"}, "c", Location{"s2"}),
		   TATransition(Location{"s2"}, "d", Location{"s1"}, {{"x", automata::AtomicClockConstraintT<std::equal_to<Time>>(1)}}, {"x"}),
		   TATransition(Location{"s2"}, "b", Location{"s2"})}};
	
	logic::AtomicProposition<std::string> a_AP{"a"};
	logic::AtomicProposition<std::string> b_AP{"b"};
	logic::AtomicProposition<std::string> c_AP{"c"};
	logic::AtomicProposition<std::string> d_AP{"d"};

	logic::MTLFormula a{a_AP};
	logic::MTLFormula b{b_AP};

	logic::MTLFormula phi1 = logic::finally(logic::globally(!a));

	auto ata = mtl_ata_translation::translate(phi1, {a_AP, b_AP, c_AP, d_AP});

	CAPTURE(ata);

	visualization::ta_to_graphviz(ta)
	  .render_to_file(fmt::format("simple_ta.pdf"));
	
	std::set<std::string> controller_actions = {"a", "b"};
	std::set<std::string> environment_actions = {"c", "d"};
	

	TreeSearch search{&ta,
					  &ata,
					  controller_actions,
					  environment_actions,
					  5,
					  true, //similar if false, every bad node is still "bad" despite not being so, everything else is just unknown
					  false, //exact same if true
					  generate_heuristic<TreeSearch::Node>(),
					  true};

	search.build_tree(true);

	CHECK(search.get_root()->label != search::NodeLabel::TOP);
}

#if true
TEST_CASE("Railroad example using zones", "[zones]")
{
	using Location [[maybe_unused]] = automata::ta::Location<std::vector<std::string>>;
	using TimedAutomaton [[maybe_unused]] = automata::ta::TimedAutomaton<Location, std::string>;

	using TAConfiguration [[maybe_unused]] = PlantConfiguration<Location>;

	using PlantState [[maybe_unused]] = search::PlantState<Location>;
	using ATAState [[maybe_unused]] = search::ATAState<std::string>;
	using CanonicalABWord [[maybe_unused]] = search::CanonicalABWord<Location, std::string>;
	using PlantZoneState [[maybe_unused]] = search::PlantZoneState<Location>;
	using ATAZoneState [[maybe_unused]] = search::ATAZoneState<std::string>;

	[[maybe_unused]] zones::Zone_slice zone_all{0, 2, false, false, 2};
	[[maybe_unused]] zones::Zone_slice zone_eq0{0, 0, false, false, 2};

	logic::AtomicProposition<std::string> enter_1{"enter_1"};
	logic::AtomicProposition<std::string> finish_close_1{"finish_close_1"};
	logic::AtomicProposition<std::string> finish_open_1{"finish_open_1"};
	logic::AtomicProposition<std::string> start_open_1{"start_open_1"};
	logic::AtomicProposition<std::string> leave_1{"leave_1"};
	logic::AtomicProposition<std::string> travel_1{"travel_1"};

	logic::MTLFormula e{enter_1};
	logic::MTLFormula f_c{finish_close_1};
	logic::MTLFormula s_o{start_open_1};
	logic::MTLFormula l{leave_1};
	logic::MTLFormula t{travel_1};
	logic::MTLFormula f_o{finish_open_1};

	logic::MTLFormula phi1 = e.dual_until(!f_c);
	logic::MTLFormula phi2 = s_o.dual_until(!l);
	logic::MTLFormula phi3 = t.dual_until(!f_o);

	//~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~START~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~//

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

	CHECK(K == 2);

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

	auto controller = controller_synthesis::create_controller(
						search.get_root(), controller_actions, environment_actions, 2
						);
	
	CHECK(search::verify_ta_controller(plant, controller, spec, K));

	#if true
	[[maybe_unused]] const int num_crossings = 2;
	#if USE_INTERACTIVE_VISUALIZATION
		char              tmp_filename[] = "search_graph_XXXXXX.svg";
		mkstemps(tmp_filename, 4);
		std::filesystem::path tmp_file(tmp_filename);
		visualization::search_tree_to_graphviz_interactive(search.get_root(), tmp_filename);
	#else
		visualization::search_tree_to_graphviz(*search.get_root(), false)
		  .render_to_file(fmt::format("railroad{}.svg", num_crossings));
	#endif
	
	visualization::ta_to_graphviz(controller,
								  false)
	  .render_to_file(fmt::format("railroad{}_controller.pdf", num_crossings));
	#endif
}
#endif

} // namespace