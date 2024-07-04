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
using Transition     = automata::ta::Transition<std::string, std::string>;
using Location       = automata::ta::Location<std::string>;

TEST_CASE("Getting fulfilled Clock Constraints", "[zones]")
{
	automata::ClockConstraint c1 = automata::AtomicClockConstraintT<std::less<Time>>(1);
	automata::ClockConstraint c2 = automata::AtomicClockConstraintT<std::greater<Time>>(1);
	automata::ClockConstraint c3 = automata::AtomicClockConstraintT<std::equal_to<Time>>(1);

	TimedAutomaton ta{{"a", "b"}, Location{"s0"}, {Location{"s0"}, Location{"s1"}}};
	ta.add_clock("x");
	ta.add_transition(Transition(Location{"s0"}, "a", Location{"s0"}, {{"x", c1}, {"x", c2}}));
	ta.add_transition(Transition(Location{"s0"}, "b", Location{"s1"}, {{"x", c3}}));

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

} // namespace

