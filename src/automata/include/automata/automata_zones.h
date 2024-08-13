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
		//If the upper_bound is equal to the max_constant (so the upper bound isn't strict), it is assumed that the upperbound is positive infinity. If max_constant
		//is 0, there is no max constant
		Endpoint max_constant_;

		/** Constructor for Zone slice. If upper_bound is larger than the max_constant, it is set back to the max_constant */
		Zone_slice(Endpoint lower_bound, Endpoint upper_bound, bool lower_isStrict, bool upper_isStrict, Endpoint max_constant) :
			lower_bound_(lower_bound), 
			upper_bound_(upper_bound), 
			lower_isOpen_(lower_isStrict), 
			upper_isOpen_(upper_isStrict),
			max_constant_(max_constant)
		{
			if(upper_bound_ > max_constant_) {
				upper_bound_ = max_constant_;
				upper_isOpen_ = false;
			}
		}

		/** Construct using a ClockConstraint, the actual definition of a zone */
		Zone_slice(automata::ClockConstraint clock_constraint, Endpoint max_constant)
		{
			Endpoint constant = std::visit([](const auto &atomic_clock_constraint)
						  -> Time { return atomic_clock_constraint.get_comparand(); },
						  clock_constraint); //Visit due to ClockConstraint being a variant

			max_constant_ = max_constant;

			std::optional<int> relation_opt = automata::get_relation_index(clock_constraint);
			assert(relation_opt.has_value());
			int relation = relation_opt.value();

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
				upper_bound_ = max_constant_;
				lower_isOpen_ = false;
				upper_isOpen_ = false;
				break;
			case 5: //greater
				lower_bound_ = constant;
				upper_bound_ = max_constant_;
				lower_isOpen_ = true;
				upper_isOpen_ = false;
				break;
			default: //not_equal or other oopsie (We assume inequality constraints don't exist for zones)
				assert(false);
				break;
			}

			if(upper_bound_ > max_constant_) {
				upper_bound_ = max_constant_;
				upper_isOpen_ = false;
			}

			if(lower_bound_ > max_constant_) {
				lower_bound_ = max_constant_;
				lower_isOpen_ = true;
			}
		}

		/**
		 * Create a Zone_slice using multiple constraints (i.e. in a conjunction) for a specific clock.
		 */
		Zone_slice(const std::multimap<std::string, automata::ClockConstraint> constraints, std::string clock, Endpoint max_constant)
		{
			lower_bound_ = 0;
			upper_bound_ = max_constant;
			lower_isOpen_ = false;
			upper_isOpen_ = false;
			max_constant_ = max_constant;

			if(!constraints.empty()) {
				this->conjunct(constraints, clock);
			}

			if(upper_bound_ > max_constant_) {
				upper_bound_ = max_constant_;
				upper_isOpen_ = false;
			}
		}

		/** Returns true if a valuation is in this zone, otherwise returns false */
		bool is_in_zone(ClockValuation valuation) const
		{
			return
				(valuation == (ClockValuation) lower_bound_ && !lower_isOpen_) ||
				(valuation == (ClockValuation) upper_bound_ && !upper_isOpen_) ||
				(valuation >  (ClockValuation) lower_bound_ && (valuation < (ClockValuation) upper_bound_ || upper_bound_ >= max_constant_));
		}

		/** Returns true if zone2 is a subset of this zone, otherwise returns false
		 * 
		 * @param zone2 The zone that is supposed to be a subset
		 * @return True iff zone2 is a subset of this zone
		 */
		bool contains_zone(Zone_slice zone2) const
		{
			return
				(lower_bound_ < zone2.lower_bound_ || (lower_bound_ == zone2.lower_bound_ && ((lower_isOpen_ && zone2.lower_isOpen_) || !lower_isOpen_))) &&
				(upper_bound_ > zone2.upper_bound_ || (upper_bound_ == zone2.upper_bound_ && ((upper_isOpen_ && zone2.upper_isOpen_) || !upper_isOpen_))) &&
				(max_constant_ >= zone2.max_constant_);
		}

		/** Returns true if this zone represents the empty set */
		bool is_empty() const
		{
			return lower_bound_ > upper_bound_ ||
				  (lower_bound_ == upper_bound_ && (lower_isOpen_ && upper_isOpen_));
		}

		/**
		 * Conjuncts this zone slice with a clock constraint.
		 * 
		 * I.e. This zone is intersected with the zone associated with the clock constraint.
		 * 
		 * @param constraint The clock constraint representing the other zone
		 */
		void conjunct(automata::ClockConstraint constraint)
		{
			Zone_slice zone2{constraint, this->max_constant_};
			this->intersect(zone2);
		}

		/**
		 * Conjunct several clock constraints with this zone slice
		 * 
		 * @param constraints Multimap of clock constraints that are conjuncted with this zone
		 * @param clock Name of the clock from which the clock constraints should be taken from
		 */
		void conjunct(std::multimap<std::string, automata::ClockConstraint> constraints, std::string clock)
		{
			if(constraints.empty()) {
				return;
			}

			for(auto iter1 = constraints.begin(); iter1 != constraints.end(); iter1++) {
				if(iter1->first == clock) {
					this->conjunct(iter1->second);
				}
			}
		}

		/**
		 * Intersects the current zone_slice with another zone slice zone2.
		 * 
		 * Standard set definition for intervals apply. The smaller max_constant is taken.
		 */
		void intersect(const Zone_slice &zone2)
		{
			//If the intersection is empty, we just make it to (0;0) to represent the empty set, however leaving it invalid should be fine
			if((lower_bound_ > zone2.upper_bound_ || upper_bound_ < zone2.lower_bound_) || is_empty() || zone2.is_empty()) {
				lower_bound_ = 0;
				upper_bound_ = 0;
				lower_isOpen_ = true;
				upper_isOpen_ = true;
				return;
			}

			if(lower_bound_ <= zone2.lower_bound_)
			{
				lower_bound_ = zone2.lower_bound_;
				lower_isOpen_ = zone2.lower_isOpen_ || lower_isOpen_;
			}

			if(upper_bound_ >= zone2.upper_bound_)
			{
				upper_bound_ = zone2.upper_bound_;
				upper_isOpen_ = zone2.upper_isOpen_ || upper_isOpen_;
			}

			if(max_constant_ > zone2.max_constant_) {
				max_constant_ = zone2.max_constant_;
			}
		}

		/**
		 * Resets this zone by setting it to the closed interval from 0 to 0 [0;0]
		 */
		void reset()
		{
			//Do not reset empty zones.
			if(is_empty()) {
				return;
			}

			lower_bound_ = 0;
			upper_bound_ = 0;
			lower_isOpen_ = false;
			upper_isOpen_ = false;
		}

		/** Compare two symbolic states.
		 * @param s1 The first state
		 * @param s2 The second state
		 * @return true if s1 is lexicographically smaller than s2
		 */
		friend bool
		operator<(const Zone_slice &s1, const Zone_slice &s2) //Use forward_as_tuple instead of tie due to rvalues
		{
			//Logical negation, since strict is usually smaller, and false == 0. Not really that important
			return std::forward_as_tuple(s1.lower_bound_, s1.upper_bound_, !s1.lower_isOpen_, !s1.upper_isOpen_, s1.max_constant_)
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
	 * Kind of a trivial check now that empty sets can be represented by "invalid" zones.
	 * 
	 * @param zone Zone to be checked
	 * @return Returns true if zone is valid
	 */
	bool
	is_valid_zone(const Zone_slice &zone);

	/**
	 * @brief Get a multimap of all fulfilled clock constraints by some specific valuation. This corresponds to the set of all zones' constraints
	 * that fulfill this valuation.
	 * 
	 * @param allConstraints Multimap containing all clock constraints that should be checked with the valuation. The key is the clock and the value
	 * is a clock constraint.	
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

	/** Checks whether a clock constraint is satisfied by a zone.
	 * A Zone satisfies a clock constraint if all valuations in the zone satisfy the constraint.
	 * 
	 * @param constraint The clock constraint
	 * @param zone The zone
	 * @return True if all valuations in the zone satisfy the clock constraint
	 */
	bool
	is_satisfied(const automata::ClockConstraint &constraint, const Zone_slice &zone);

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