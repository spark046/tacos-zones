#ifndef SRC_AUTOMATA_INCLUDE_AUTOMATA_AUTOMATA_ZONES_H
#define SRC_AUTOMATA_INCLUDE_AUTOMATA_AUTOMATA_ZONES_H

#include "utilities/types.h"

#include "automata.h"
#include "ta.h"

//TODO: I have no idea which of these libraries are needed for formatting
#include <boost/format.hpp>
#include <functional>
#include <iostream>
#include <map>
#include <optional>
#include <set>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>
#include <vector>

#include <limits>

	namespace tacos::zones {

	/**
	 * Struct modeling the set of valuations of a zone for an atomic clock constraint (i.e. no conjunctions)
	 */
	struct Zone_slice
	{
		Endpoint lower_bound_;
		Endpoint upper_bound_;
		bool lower_isStrict_;
		bool upper_isStrict_;

		Zone_slice(Endpoint lower_bound, Endpoint upper_bound, bool lower_isStrict, bool upper_isStrict) :
			lower_bound_(lower_bound), 
			upper_bound_(upper_bound), 
			lower_isStrict_(lower_isStrict), 
			upper_isStrict_(upper_isStrict)
		{

		}

		/** Construct using a ClockConstraint, the actual definition of a zone */
		Zone_slice(automata::ClockConstraint clock_constraint)
		{
			Endpoint constant = std::visit([](const auto &atomic_clock_constraint)
						  -> Time { return atomic_clock_constraint.get_comparand(); },
						  clock_constraint); //Visit due to ClockConstraint being a variant

			std::optional<int> relation_opt = automata::get_relation_index(clock_constraint);
			assert(relation_opt.has_value());
			int relation = relation_opt.value();

			switch (relation)
			{
			case 0: //less
				lower_bound_ = 0;
				upper_bound_ = constant;
				lower_isStrict_ = false;
				upper_isStrict_ = true;
				break;
			case 1: //less_equal
				lower_bound_ = 0;
				upper_bound_ = constant;
				lower_isStrict_ = false;
				upper_isStrict_ = false;
				break;
			case 2: //equal_to
				lower_bound_ = constant;
				upper_bound_ = constant;
				lower_isStrict_ = false;
				upper_isStrict_ = false;
				break;
			case 4: //greater_equal
				lower_bound_ = constant;
				upper_bound_ = std::numeric_limits<Endpoint>::max();
				lower_isStrict_ = false;
				upper_isStrict_ = false;
				break;
			case 5: //greater
				lower_bound_ = constant;
				upper_bound_ = std::numeric_limits<Endpoint>::max();
				lower_isStrict_ = true;
				upper_isStrict_ = false;
				break;
			default: //not_equal or other oopsie (We assume inequality constraints don't exist for zones)
				assert(false);
				break;
			}
		}

		/**
		 * Create a Zone_slice using multiple constraints (i.e. in a conjunction) for a specific clock.
		 */
		Zone_slice(const std::multimap<std::string, automata::ClockConstraint> constraints, std::string clock)
		{
			lower_bound_ = 0;
			upper_bound_ = std::numeric_limits<Endpoint>::max();
			lower_isStrict_ = false;
			upper_isStrict_ = false;

			//Go through all constraints and conjunct the ones which match to the clock
			for(auto constraint = constraints.begin(); constraint != constraints.end(); constraint++)
			{
				if(constraint->first == clock)
				{
					this->conjunct(constraint->second);
				}
			}
		}

		/** Returns true if a valuation is in this zone, otherwise returns false */
		bool is_in_zone(ClockValuation valuation)
		{
			return
				(valuation == (ClockValuation) lower_bound_ && !lower_isStrict_) ||
				(valuation == (ClockValuation) upper_bound_ && !upper_isStrict_) ||
				(valuation >  (ClockValuation) lower_bound_ && valuation < (ClockValuation) upper_bound_);
		}

		/**
		 * Conjuncts this zone slice with a clock constraint.
		 * 
		 * I.e. This zone is intersected with the zone associated with the clock constraint.
		 * 
		 * @param constraint: automata::ClockConstraint The clock constraint representing the other zone
		 */
		void conjunct(automata::ClockConstraint constraint)
		{
			Zone_slice zone2 = Zone_slice(constraint);
			this->intersect(zone2);
		}

		/**
		 * Intersects the current zone_slice with another zone slice zone2.
		 * 
		 * Standard set definition for intervals apply.
		 */
		void intersect(const Zone_slice &zone2)
		{
			//TODO: Add proper handling
			assert(!(lower_bound_ > zone2.upper_bound_ || upper_bound_ < zone2.lower_bound_)); //If the intersetion is empty, we don't want this

			if(lower_bound_ < zone2.lower_bound_)
			{
				lower_bound_ = zone2.lower_bound_;
				lower_isStrict_ = zone2.lower_isStrict_;
			} else if(lower_bound_ == zone2.lower_bound_) {
				lower_isStrict_ = lower_isStrict_ || zone2.lower_isStrict_;
			}

			if(upper_bound_ > zone2.upper_bound_)
			{
				upper_bound_ = zone2.upper_bound_;
				upper_isStrict_ = zone2.upper_isStrict_;
			} else if(upper_bound_ == zone2.upper_bound_) {
				upper_isStrict_ = upper_isStrict_ || zone2.upper_isStrict_;
			}
		}

		/** Compare two symbolic states.
		 * @param s1 The first state
		 * @param s2 The second state
		 * @return true if s1 is lexicographically smaller than s2
		 */
		friend bool
		operator<(const Zone_slice &s1, const Zone_slice &s2) //Use forward_as_tuple instead of tie due to rvalues
		{
			return std::forward_as_tuple(s1.lower_bound_, s1.upper_bound_, !s1.lower_isStrict_, !s1.upper_isStrict_) //Logical negation, since strict is usually smaller, and false == 0. Not really that important
			       < std::forward_as_tuple(s2.lower_bound_, s2.upper_bound_, !s2.lower_isStrict_, !s2.upper_isStrict_);
		}

		/** Check two symbolic states for equality.
		 * Two symbolic states are considered equal if they have the same location(, clock name), and
		 * symbolic time.
		 * @param s1 The first state
		 * @param s2 The second state
		 * @return true if s1 is equal to s2
		 */
		friend bool
		operator==(const Zone_slice &s1, const Zone_slice &s2) {
			return !(s1 < s2) && !(s2 < s1);
		}
	};

	std::ostream &
	operator<<(std::ostream &os, const zones::Zone_slice &zone_slice);

	std::ostream &
	operator<<(std::ostream &os, const std::map<std::string, tacos::zones::Zone_slice> &zone);

	/** @brief Given a RegionIndex, compute the set of clock constraints that belong to this index.
	 * This index fulfills the following properties:
	 * -The index is even iff the set only contains equality clock constraints (e.g. x = 3) [Ensures that if fractional part is equal to zero, then region index is even]
	 * -The set of clock constraints are normalized by some constant K so that there is only a finite amount of them => If there are n clock constraints, then the maximum index is 2^n
	 * -They are ordered in such a way, so that incrementing them makes some sense, similar to incrementing normal region indices (probably add a function that calculates the "next" zone), in other words time advances. Maybe make incrementation the Delay?
	 * TODO: Figure out other properties that a RegionIndex needs to fulfill
	 * -The order is otherwise given by a set order of clock constraints and then the power set construction for this (i.e. from smallest set to biggest set)
	 * 
	 * @param region_index The region index to construct the constraint for
	 * @param max_region_index The maximal region index that may occur
	 * @param bound_type Whether to construct lower, upper, or both bounds
	 * @return A set (with either one or two elements) of clock constraints that restrict some clock to
	 * the given region
	 */
	std::set<automata::ClockConstraint>
	get_clock_constraints_from_region_index();

	/**
	 * @brief Returns a set of all clock constraints of a particular timed automaton
	 * This is done by iterating over all constraints.
	 * 
	 * @param timePoint The valuation that is supposed to be checked by the constraints.
	 * @return A multimap of Clock Constraints, where the key is a string corresponding to the clock for which the constraint is for, and the values are clock constraints.
	 */
	template <typename LocationT, typename AP>
	std::multimap<std::string, automata::ClockConstraint>
	get_clock_constraints_of_ta(const automata::ta::TimedAutomaton<LocationT, AP> &ta);

	/**
	 * @brief Get a multimap of all fulfilled clock constraints by some specific valuation
	 * 
	 * @param allConstraints Multimap containing all clock constraints that should be checked with the valuation. The key is the clock and the value is a clock constraint.	
	 * @param clock Name of the relevant clock
	 * @param val Valuation of the clock
	 * @return Multimap that only consists of all fulfilled constraints
	 */
	std::multimap<std::string, automata::ClockConstraint>
	get_fulfilled_clock_constraints(const std::multimap<std::string, automata::ClockConstraint> allConstraints, std::string clock, ClockValuation val);
} //namespace tacos::zones

namespace fmt {

template <>
struct formatter<std::map<std::string, tacos::zones::Zone_slice>> : ostream_formatter
{
};

template <>
struct formatter<tacos::zones::Zone_slice> : ostream_formatter
{
};

} //fmt

#include "automata_zones.hpp"

#endif