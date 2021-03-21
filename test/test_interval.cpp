/***************************************************************************
 *  test_interval.cpp - Test Interval implementation
 *
 *  Created: 4 June 2020
 *  Copyright  2020  Stefan Schupp <stefan.schupp@cs.rwth-aachen.de>
 ****************************************************************************/

/*  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation; either version 2 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU Library General Public License for more details.
 *
 *  Read the full text in the LICENSE.GPL file in the doc directory.
 */

#include "utilities/Interval.h"

#include <catch2/catch_test_macros.hpp>

namespace {
using Interval = utilities::arithmetic::Interval<int>;
using utilities::arithmetic::BoundType;

TEST_CASE("Construction of intervals", "[libmtl]")
{
	REQUIRE(Interval(2, 3).lower() == 2);
	REQUIRE(Interval(2, 3).upper() == 3);
	REQUIRE(Interval().lowerBoundType() == BoundType::INFTY);
	REQUIRE(Interval().upperBoundType() == BoundType::INFTY);
}

TEST_CASE("Interval comparison", "[libmtl]")
{
	// Less than
	CHECK(Interval(1, BoundType::WEAK, 0, BoundType::INFTY) < Interval());
	CHECK(Interval(1, BoundType::WEAK, 0, BoundType::INFTY)
	      < Interval(2, BoundType::WEAK, 0, BoundType::INFTY));
	CHECK(Interval(1, BoundType::STRICT, 0, BoundType::INFTY)
	      < Interval(2, BoundType::WEAK, 0, BoundType::INFTY));
	CHECK(Interval(1, BoundType::WEAK, 0, BoundType::INFTY)
	      < Interval(1, BoundType::STRICT, 0, BoundType::INFTY));
	CHECK(Interval(0, BoundType::INFTY, 2, BoundType::WEAK)
	      < Interval(0, BoundType::INFTY, 3, BoundType::WEAK));
	CHECK(Interval(0, BoundType::INFTY, 2, BoundType::STRICT)
	      < Interval(0, BoundType::INFTY, 3, BoundType::STRICT));
	CHECK(Interval(0, BoundType::INFTY, 1, BoundType::WEAK)
	      < Interval(0, BoundType::INFTY, 1, BoundType::STRICT));
	// Value is ignored if bound type is INFTY.
	CHECK(Interval(6, BoundType::INFTY, 2, BoundType::WEAK)
	      < Interval(0, BoundType::INFTY, 3, BoundType::WEAK));

	CHECK(Interval() > Interval(1, BoundType::WEAK, 0, BoundType::INFTY));

	// Equality
	CHECK(Interval() == Interval());
	CHECK(Interval(1, BoundType::WEAK, 0, BoundType::INFTY) != Interval());
	CHECK(Interval(1, BoundType::WEAK, 0, BoundType::INFTY)
	      != Interval(1, BoundType::STRICT, 0, BoundType::INFTY));
	CHECK(Interval(1, BoundType::INFTY, 0, BoundType::INFTY) == Interval());
}

TEST_CASE("Emptiness", "[libmtl]")
{
	REQUIRE(!Interval(2, 3).is_empty());
	REQUIRE(!Interval(3, 3).is_empty());
	REQUIRE(!Interval(2, BoundType::STRICT, 3, BoundType::WEAK).is_empty());
	REQUIRE(!Interval(2, BoundType::WEAK, 3, BoundType::STRICT).is_empty());
	REQUIRE(!Interval(2, BoundType::STRICT, 3, BoundType::STRICT).is_empty());
	REQUIRE(!Interval(2, BoundType::INFTY, 3, BoundType::WEAK).is_empty());
	REQUIRE(!Interval(2, BoundType::WEAK, 3, BoundType::INFTY).is_empty());
	REQUIRE(!Interval(2, BoundType::INFTY, 3, BoundType::STRICT).is_empty());
	REQUIRE(!Interval(2, BoundType::STRICT, 3, BoundType::INFTY).is_empty());
	REQUIRE(!Interval().is_empty());

	REQUIRE(Interval(3, 2).is_empty());
	REQUIRE(Interval(2, BoundType::STRICT, 2, BoundType::WEAK).is_empty());
	REQUIRE(Interval(2, BoundType::WEAK, 2, BoundType::STRICT).is_empty());
	REQUIRE(Interval(2, BoundType::STRICT, 2, BoundType::STRICT).is_empty());
}

TEST_CASE("Containment of values", "[libmtl]")
{
	REQUIRE(Interval(2, 3).contains(2));
	REQUIRE(Interval(2, 3).contains(3));
	REQUIRE(Interval(2, BoundType::WEAK, 3, BoundType::INFTY).contains(2));
	REQUIRE(Interval(2, BoundType::INFTY, 3, BoundType::WEAK).contains(3));
	REQUIRE(Interval().contains(2));
	REQUIRE(Interval(3, BoundType::INFTY, 2, BoundType::INFTY).contains(2));
	REQUIRE(Interval(3, BoundType::INFTY, 2, BoundType::INFTY).contains(4));

	REQUIRE(!Interval(2, BoundType::STRICT, 3, BoundType::INFTY).contains(2));
	REQUIRE(!Interval(2, BoundType::INFTY, 3, BoundType::STRICT).contains(3));
	REQUIRE(!Interval(2, BoundType::STRICT, 2, BoundType::STRICT).contains(2));
}

} // namespace
