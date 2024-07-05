#ifndef SRC_AUTOMATA_INCLUDE_AUTOMATA_AUTOMATA_ZONES_H
#define SRC_AUTOMATA_INCLUDE_AUTOMATA_AUTOMATA_ZONES_H

#include "utilities/types.h"

#include "automata.h"
#include "ta.h"
#include "ata.h"

namespace tacos::zones {
	
	//struct AutomatonZones
	//{
	//	/* Maximum constant which can appear in the clock constraints of the zone */
	//	unsigned int maximum_constant;
	//
	//	/* Set of clock constraints, which constitute the zone. I.e. the zone is the set of valuations that satisfy all clock constraints in this set */
	//	RegionIndex get_clock_constraints(ClockValuation timePoint);
	//};

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
	 * 
	 * This is done by iterating over all transitions.
	 * 
	 * @param ta The automaton in question.
	 * @return A multimap of Clock Constraints, where the key is a string corresponding to the clock for which the constraint is for, and the values are clock constraints.
	 */
	template <typename LocationT, typename AP>
	std::multimap<std::string, automata::ClockConstraint>
	get_clock_constraints_of_ta(const automata::ta::TimedAutomaton<LocationT, AP> &ta);

	/**
	 * @brief Returns a set of all clock constraints of a particular alternating timed automaton
	 * 
	 * This is done by iterating over all transitions.
	 * For consistency with other functions, each clock constraint is still assigned a clock, just that this clock's name will be an emtpy string.
	 * 
	 * @param ta The automaton in question.
	 * @return A multimap of Clock Constraints, where the key is a string corresponding to the clock for which the constraint is for, and the values are clock constraints.
	 */
	template <typename LocationT, typename AP>
	std::multimap<std::string, automata::ClockConstraint>
	get_clock_constraints_of_ata(const automata::ata::AlternatingTimedAutomaton<LocationT, AP> &ata);

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

	template<typename ThisIsString>
	std::string
	test() {
		ThisIsString s = "Test";

		return s;
	}
} //namespace tacos::zones

#include "automata_zones.hpp"

#endif