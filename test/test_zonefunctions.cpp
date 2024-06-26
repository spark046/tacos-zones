#include "automata/automata.h"
#include "automata/automata_zones.h"

#include <catch2/catch_test_macros.hpp>

namespace {

using namespace tacos;
using namespace automata;
using namespace automata::zones;

using Configuration  = TAConfiguration<std::string>;
using TimedAutomaton = TimedAutomaton<std::string, std::string>;
using Transition     = Transition<std::string, std::string>;
using Location       = Location<std::string>;

TEST_CASE("Getting Clock Constraints", "[ta]")
{
	ClockConstraint c1 = AtomicClockConstraintT<std::less<Time>>(1);
	ClockConstraint c2 = AtomicClockConstraintT<std::greater<Time>>(1);
	ClockConstraint c3 = AtomicClockConstraintT<std::equal_to<Time>>(1);

	TimedAutomaton ta{{"a", "b"}, Location{"s0"}, {Location{"s0"}, Location{"s1"}}};
	ta.add_clock("x");
	ta.add_transition(Transition(Location{"s0"}, "a", Location{"s0"}, {{"x", c1}, {"x", c2}}));
	ta.add_transition(Transition(Location{"s0"}, "b", Location{"s1"}, {{"x", c3}}));

	CHECK(get_clock_constraints_of_ta(ta) == {{"x", c1}, {"x", c2}, {"x", c3}});

	CHECK(get_fulfilled_clock_constraints(get_clock_constraints_of_ta(ta), "x", 0) == {{"x", c1}});
}

} // namespace
