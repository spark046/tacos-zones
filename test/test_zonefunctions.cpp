#include "automata/automata.h"
#include "automata/automata_zones.h"
#include "automata/ta.h"
#include "utilities/types.h"
#include "automata/ta_regions.h"

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

} // namespace

