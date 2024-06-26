#include "automata_zones.h"

namespace tacos::automata::zones {

	/**
	 * @brief Returns a set of all clock constraints of a particular timed automaton
	 * This is done by iterating over all constraints.
	 * 
	 * @param timePoint The valuation that is supposed to be checked by the constraints.
	 * @return A multimap of Clock Constraints, where the key corresponds to the clock for whicht the constraint is for std::set<ClockConstraint> 
	 */
	template <typename LocationT, typename AP>
	std::multimap<std::string, ClockConstraint>
	get_clock_constraints_of_ta(const ta::TimedAutomaton<LocationT, AP> &ta) {
		//multimap to be returned
		std::multimap<std::string, ClockConstraint> ret = {};

		std::multimap<LocationT, ta::Transition> transitions = ta.get_transitions();
		std::set<std::string> clocks = ta.get_clocks();

		//iterate over all transitions to find all constraints for each clock
		for(const auto &[location, transition] : transitions) {
			std::multimap<std::string, ClockConstraint> guards = transition.get_guards();
			ret.insert(guards);
		}
		
		return ret;
	}

	/**
	 * @brief Get a multimap of all fulfilled clock constraints by some specific valuation
	 * 
	 * @param allConstraints Multimap containing all clock constraints that should be checked with the valuation. The key is the clock and the value is a clock constraint.	
	 * @param clock Name of the relevant clock
	 * @param val Valuation of the clock
	 * @return Multimap that only consists of all fulfilled constraints
	 */
	std::multimap<std::string, ClockConstraint>
	get_fulfilled_clock_constraints(const std::multimap<std::string, ClockConstraint> allConstraints, std::string clock, ClockValuation val) {
		std::multimap<std::string, ClockConstraint> ret = {};

		for(auto it1 = allConstraints.begin(); it1 != allConstraints.end(); it1++) {
			if(it1->first == clock) {
				if(automata::is_satisfied(it1->second, val)) {
					ret.insert(*it1);
				}
			}
		}

		return ret;
	}

	//TODO
	/**
	 * @brief Calculates the index for a set of clock constraints for the zone (alternating) timed automaton
	 * 
	 * @param timePoint 
	 * @return RegionIndex 
	 */
	RegionIndex
	get_clock_constraints(ClockValuation timePoint) {

	}

} // namespace tacos::automata
