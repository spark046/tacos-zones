#include "automata/automata.h"
#include "automata/automata_zones.h"
#include "automata/ta.h"
#include "utilities/types.h"
#include "automata/ta_regions.h"

#include "search/search.h"

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

TEST_CASE("Getting fulfilled Clock Constraints", "[zones]")
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

	CHECK(zones::get_clock_constraints_of_ta<std::string, std::string>(ta) == set1);

	CHECK(zones::get_fulfilled_clock_constraints(zones::get_clock_constraints_of_ta<std::string, std::string>(ta), "x", 0) == set2);
}

TEST_CASE("Delaying zones of zone states", "[zones]")
{
	std::multimap<std::string, automata::ClockConstraint> zone1 = {{"x", automata::AtomicClockConstraintT<std::greater<Time>>(1)}};

	std::multimap<std::string, automata::ClockConstraint> zone2 = { {"x", automata::AtomicClockConstraintT<std::greater<Time>>(1)},
																	{"x", automata::AtomicClockConstraintT<std::less<Time>>(2)}};

	std::multimap<std::string, automata::ClockConstraint> zone3 = { {"x", automata::AtomicClockConstraintT<std::equal_to<Time>>(1)},
																	{"x", automata::AtomicClockConstraintT<std::not_equal_to<Time>>(2)}};

	std::multimap<std::string, automata::ClockConstraint> zone4 = { {"x", automata::AtomicClockConstraintT<std::greater_equal<Time>>(1)}};

	search::PlantZoneState<std::string> ta_state1 = {"l0", "x", zone1};
	CHECK(ta_state1.get_increment_valuation() == zone1);

	search::PlantZoneState<std::string> ta_state2 = {"l0", "x", zone2};
	CHECK(ta_state2.get_increment_valuation() == zone1);

	search::PlantZoneState<std::string> ta_state3 = {"l0", "x", zone3};
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

} // namespace

