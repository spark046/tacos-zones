#pragma once

#include "automata_zones.h"

namespace tacos::zones {
	template <typename LocationT, typename AP>
	std::multimap<std::string, automata::ClockConstraint>
	get_clock_constraints_of_ta(const automata::ta::TimedAutomaton<LocationT, AP> &ta) {
		using Location = automata::ta::Location<LocationT>;
		using Transition = automata::ta::Transition<LocationT, AP>;

		//multimap to be returned
		std::multimap<std::string, automata::ClockConstraint> ret = {};

		std::multimap<Location, Transition> transitions = ta.get_transitions();
		std::set<std::string> clocks = ta.get_clocks();

		//iterate over all transitions to find all constraints for each clock
		for(const auto &[location, transition] : transitions) {
			std::multimap<std::string, automata::ClockConstraint> guards = transition.get_guards();
			ret.insert(guards.begin(), guards.end());
		}
		
		return ret;
	}
} // namespace tacos::zones
