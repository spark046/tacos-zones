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

	template <typename LocationT, typename AP>
	std::multimap<std::string, automata::ClockConstraint>
	get_clock_constraints_of_ata(const automata::ata::AlternatingTimedAutomaton<LocationT, AP> &ata) {
		using Transition = automata::ata::Transition<LocationT, AP>;
		using Formula = automata::ata::Formula<LocationT>;
		using ClockConstraintFormula = automata::ata::ClockConstraintFormula<LocationT>;

		//multimap to be returned
		std::multimap<std::string, automata::ClockConstraint> ret = {};

		std::set<Transition> transitions = ata.get_transitions();

		for(auto iter1 = transitions.begin(); iter1 != transitions.end(); iter1++)
		{
			Formula *formula = iter1.get_formula();

			dynamic_cast<ClockConstraintFormula*> (formula);
			if(formula != NULL)
			{
				ret.insert("", formula.get_constraint());
			}
		}
		
		return ret;
	}
} // namespace tacos::zones
