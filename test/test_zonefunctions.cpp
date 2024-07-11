#include "automata/automata.h"
#include "automata/automata_zones.h"
#include "automata/ta.h"
#include "automata/ata.h"
#include "mtl_ata_translation/translator.h"
#include "mtl/MTLFormula.h"
#include "utilities/types.h"
#include "automata/ta_regions.h"

#include "search/search.h"

#include <catch2/catch_test_macros.hpp>
#include <map>
#include <string>

namespace {

using namespace tacos;

using AP = logic::AtomicProposition<std::string>;
using Configuration  = automata::ta::TAConfiguration<std::string>;
using TimedAutomaton = automata::ta::TimedAutomaton<std::string, std::string>;
using AlternatingTimedAutomaton = automata::ata::AlternatingTimedAutomaton<std::string, std::string>;
using TATransition   = automata::ta::Transition<std::string, std::string>;
using ATATransition  = automata::ata::Transition<std::string, std::string>;
using Location       = automata::ta::Location<std::string>;

using ::utilities::arithmetic::BoundType;

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

TEST_CASE("Getting Canonical Word with zones", "[zones]")
{
	TimedAutomaton ta{{"a", "b"}, Location{"l0"}, {Location{"l0"}, Location{"l1"}}};
	ta.add_clock("x");
	ta.add_transition(TATransition(Location{"l0"},
	                               "a",
	                               Location{"l0"},
	                               {{"x", automata::AtomicClockConstraintT<std::greater<Time>>(1)}},
	                               {"x"}));
	ta.add_transition(TATransition(
	  Location{"l0"}, "b", Location{"l1"}, {{"x", automata::AtomicClockConstraintT<std::less<Time>>(1)}}));

	logic::MTLFormula<std::string> a{AP("a")};
	logic::MTLFormula<std::string> b{AP("b")};

	logic::MTLFormula spec = a.until(b, logic::TimeInterval{2, BoundType::WEAK, 2, BoundType::INFTY});
	auto              ata  = mtl_ata_translation::translate(spec, {AP{"a"}, AP{"b"}});

	std::set<automata::ata::Transition<logic::MTLFormula<std::string>, logic::AtomicProposition<std::string>>> transitions = ata.get_transitions();
}

} // namespace

