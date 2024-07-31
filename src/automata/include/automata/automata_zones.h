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
		//It is better to not manually set this, as upper_bound should always be less or equal to the max_constant, which may not be guaranteed if done manually
		Endpoint upper_bound_;
		bool lower_isOpen_;
		bool upper_isOpen_;
		//If the upper_bound is equal to the max_constant (so the upper bound isn't strict), it is assumed that the upperbound is positive infinity. If max_constant is 0, there is no max constant
		Endpoint max_constant_;

		/** Constructor for Zone slice. If upper_bound is larger than the max_constant, it is set back to the max_constant */
		Zone_slice(Endpoint lower_bound, Endpoint upper_bound, bool lower_isStrict, bool upper_isStrict, Endpoint max_constant = 0) :
			lower_bound_(lower_bound), 
			upper_bound_(upper_bound), 
			lower_isOpen_(lower_isStrict), 
			upper_isOpen_(upper_isStrict),
			max_constant_(max_constant)
		{
			if(upper_bound_ > max_constant_ && max_constant_ > 0) {
				upper_bound_ = max_constant_;
				upper_isOpen_ = false;
			}
		}

		/** Construct using a ClockConstraint, the actual definition of a zone */
		Zone_slice(automata::ClockConstraint clock_constraint, Endpoint max_constant = 0)
		{
			Endpoint constant = std::visit([](const auto &atomic_clock_constraint)
						  -> Time { return atomic_clock_constraint.get_comparand(); },
						  clock_constraint); //Visit due to ClockConstraint being a variant

			assert(constant <= max_constant || max_constant == 0);

			std::optional<int> relation_opt = automata::get_relation_index(clock_constraint);
			assert(relation_opt.has_value());
			int relation = relation_opt.value();

			max_constant_ = max_constant;
			

			switch (relation)
			{
			case 0: //less
				lower_bound_ = 0;
				upper_bound_ = constant;
				lower_isOpen_ = false;
				upper_isOpen_ = true;
				break;
			case 1: //less_equal
				lower_bound_ = 0;
				upper_bound_ = constant;
				lower_isOpen_ = false;
				upper_isOpen_ = false;
				break;
			case 2: //equal_to
				lower_bound_ = constant;
				upper_bound_ = constant;
				lower_isOpen_ = false;
				upper_isOpen_ = false;
				break;
			case 4: //greater_equal
				lower_bound_ = constant;
				upper_bound_ = std::numeric_limits<Endpoint>::max();
				lower_isOpen_ = false;
				upper_isOpen_ = false;
				break;
			case 5: //greater
				lower_bound_ = constant;
				upper_bound_ = std::numeric_limits<Endpoint>::max();
				lower_isOpen_ = true;
				upper_isOpen_ = false;
				break;
			default: //not_equal or other oopsie (We assume inequality constraints don't exist for zones)
				assert(false);
				break;
			}

			if(upper_bound_ > max_constant_ && max_constant_ > 0) {
				upper_bound_ = max_constant_;
				upper_isOpen_ = false;
			}
		}

		/**
		 * Create a Zone_slice using multiple constraints (i.e. in a conjunction) for a specific clock.
		 */
		Zone_slice(const std::multimap<std::string, automata::ClockConstraint> constraints, std::string clock, Endpoint max_constant = 0)
		{
			lower_bound_ = 0;
			upper_bound_ = std::numeric_limits<Endpoint>::max();
			lower_isOpen_ = false;
			upper_isOpen_ = false;
			max_constant_ = max_constant;

			//Go through all constraints and conjunct the ones which match to the clock
			for(auto constraint = constraints.begin(); constraint != constraints.end(); constraint++)
			{
				if(constraint->first == clock)
				{
					this->conjunct(constraint->second);
				}
			}

			if(upper_bound_ > max_constant_ && max_constant_ > 0) {
				upper_bound_ = max_constant_;
				upper_isOpen_ = false;
			}
		}

		/** Returns true if a valuation is in this zone, otherwise returns false */
		bool is_in_zone(ClockValuation valuation)
		{
			return
				(valuation == (ClockValuation) lower_bound_ && !lower_isOpen_) ||
				(valuation == (ClockValuation) upper_bound_ && !upper_isOpen_) ||
				(valuation >  (ClockValuation) lower_bound_ && (valuation < (ClockValuation) upper_bound_ || upper_bound_ >= max_constant_));
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
		 * Standard set definition for intervals apply. The smaller max_constant is taken.
		 */
		void intersect(const Zone_slice &zone2)
		{
			//TODO: Add proper handling
			assert(!(lower_bound_ > zone2.upper_bound_ || upper_bound_ < zone2.lower_bound_)); //If the intersetion is empty, we don't want this

			if(lower_bound_ < zone2.lower_bound_)
			{
				lower_bound_ = zone2.lower_bound_;
				lower_isOpen_ = zone2.lower_isOpen_;
			} else if(lower_bound_ == zone2.lower_bound_) {
				lower_isOpen_ = lower_isOpen_ || zone2.lower_isOpen_;
			}

			if(upper_bound_ > zone2.upper_bound_)
			{
				upper_bound_ = zone2.upper_bound_;
				upper_isOpen_ = zone2.upper_isOpen_;
			} else if(upper_bound_ == zone2.upper_bound_) {
				upper_isOpen_ = upper_isOpen_ || zone2.upper_isOpen_;
			}

			if(max_constant_ > zone2.max_constant_ && zone2.max_constant_ > 0) {
				max_constant_ = zone2.max_constant_;
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
			return std::forward_as_tuple(s1.lower_bound_, s1.upper_bound_, !s1.lower_isOpen_, !s1.upper_isOpen_, s1.max_constant_) //Logical negation, since strict is usually smaller, and false == 0. Not really that important
			       < std::forward_as_tuple(s2.lower_bound_, s2.upper_bound_, !s2.lower_isOpen_, !s2.upper_isOpen_, s2.max_constant_);
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

	/**
	 * @brief Checks whether a zone's interval is valid, i.e. lower bound is less equal to upper bound, and no bounds exceed the max constant
	 * 
	 * @param zone Zone to be checked
	 * @return Returns true if zone is valid
	 */
	bool
	is_valid_zone(const Zone_slice &zone);

	/**
	 * @brief Get a multimap of all fulfilled clock constraints by some specific valuation. This corresponds to the set of all zones' constraints that fulfill this valuation.
	 * 
	 * @param allConstraints Multimap containing all clock constraints that should be checked with the valuation. The key is the clock and the value is a clock constraint.	
	 * @param clock Name of the relevant clock
	 * @param val Valuation of the clock
	 * @return Multimap that only consists of all fulfilled constraints
	 */
	std::multimap<std::string, automata::ClockConstraint>
	get_fulfilled_clock_constraints(const std::multimap<std::string, automata::ClockConstraint> allConstraints, std::string clock, ClockValuation val);

	/**
	 * Translates a zone slice back to a set of clock constraints.
	 * 
	 * @param zone Zone_slice to be converted back
	 * @param max_region_index Max constant encoded in the form of a RegionIndex
	 * @return A vector of ClockConstraints that constraint valuations to exactly this zone
	 */
	std::vector<automata::ClockConstraint> 
	get_clock_constraints_from_zone(const Zone_slice &zone, RegionIndex max_region_index);
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