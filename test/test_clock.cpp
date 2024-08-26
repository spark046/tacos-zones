/***************************************************************************
 *  test_clock.cpp - Test the Clock class
 *
 *  Created:   Tue  9 Feb 12:48:44 CET 2021
 *  Copyright  2021  Till Hofmann <hofmann@kbsg.rwth-aachen.de>
 *  SPDX-License-Identifier: LGPL-3.0-or-later
 ****************************************************************************/


#include "automata/automata.h"

#include <catch2/catch_test_macros.hpp>

namespace {

using namespace tacos;

TEST_CASE("Clock initialization", "[automata]")
{
	CHECK(Clock{}.get_valuation() == 0);
	CHECK(Clock{5}.get_valuation() == 5);
}

TEST_CASE("Clock time progression", "[automata]")
{
	Clock c;
	CHECK(c.get_valuation() == 0);
	c.tick(2.5);
	CHECK(c.get_valuation() == 2.5);
	c.reset();
	CHECK(c.get_valuation() == 0);
}

TEST_CASE("Clock implicit conversion to time", "[automata]")
{
	CHECK(Clock{} == Time{0});
	CHECK(Clock{0.1} == Time{0.1});
}

TEST_CASE("Conjunction of Clock constraint satisfiability", "[automata]")
{
	std::multimap<std::string, automata::ClockConstraint> constraints1{
		{"x", automata::AtomicClockConstraintT<std::less<Time>>(3)},
		{"x", automata::AtomicClockConstraintT<std::less_equal<Time>>(5)},
		{"x", automata::AtomicClockConstraintT<std::greater_equal<Time>>(2)},
		{"y", automata::AtomicClockConstraintT<std::less<Time>>(2)},
		{"y", automata::AtomicClockConstraintT<std::greater_equal<Time>>(2)}
	};

	CHECK(!automata::is_satisfiable(constraints1));

	std::multimap<std::string, automata::ClockConstraint> constraints2{
		{"x", automata::AtomicClockConstraintT<std::less<Time>>(3)},
		{"x", automata::AtomicClockConstraintT<std::less_equal<Time>>(5)},
		{"x", automata::AtomicClockConstraintT<std::equal_to<Time>>(2)},
		{"y", automata::AtomicClockConstraintT<std::less_equal<Time>>(2)},
		{"y", automata::AtomicClockConstraintT<std::greater_equal<Time>>(2)}
	};

	CHECK(automata::is_satisfiable(constraints2));

	std::multimap<std::string, automata::ClockConstraint> constraints3{
		{"x", automata::AtomicClockConstraintT<std::less<Time>>(3)},
		{"y", automata::AtomicClockConstraintT<std::less<Time>>(4)},
		{"y", automata::AtomicClockConstraintT<std::greater_equal<Time>>(3)},
	};

	CHECK(automata::is_satisfiable(constraints3));

	std::multimap<std::string, automata::ClockConstraint> constraints4{
		{"x", automata::AtomicClockConstraintT<std::less<Time>>(3)},
		{"y", automata::AtomicClockConstraintT<std::equal_to<Time>>(4)},
		{"y", automata::AtomicClockConstraintT<std::greater_equal<Time>>(3)},
	};

	CHECK(automata::is_satisfiable(constraints4));

	std::multimap<std::string, automata::ClockConstraint> constraints5{
		{"y", automata::AtomicClockConstraintT<std::less_equal<Time>>(3)},
		{"y", automata::AtomicClockConstraintT<std::greater_equal<Time>>(3)}
	};

	CHECK(automata::is_satisfiable(constraints5));

	std::multimap<std::string, automata::ClockConstraint> constraints6{
		{"y", automata::AtomicClockConstraintT<std::equal_to<Time>>(3)}
	};

	CHECK(automata::is_satisfiable(constraints6));

	std::multimap<std::string, automata::ClockConstraint> constraints7{
		{"y", automata::AtomicClockConstraintT<std::equal_to<Time>>(3)},
		{"y", automata::AtomicClockConstraintT<std::greater<Time>>(3)}
	};

	CHECK(!automata::is_satisfiable(constraints7));
}

} // namespace
