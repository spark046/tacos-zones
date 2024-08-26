/***************************************************************************
 *  automata.cpp - Generic automata definitions
 *
 *  Created: Thu 28 May 2020 15:46:12 CEST 15:46
 *  Copyright  2020  Till Hofmann <hofmann@kbsg.rwth-aachen.de>
 *  SPDX-License-Identifier: LGPL-3.0-or-later
 ****************************************************************************/

#include "automata/automata.h"

namespace tacos::automata {

bool
is_satisfied(const ClockConstraint &constraint, const Time &valuation)
{
	return std::visit([&](auto &&c) { return c.is_satisfied(valuation); }, constraint);
}

bool
is_satisfiable(const std::multimap<std::string, ClockConstraint> &constraints)
{
	std::map<std::string, Endpoint> min_value;
	std::map<std::string, bool>     min_strict; //False if the min value can be exactly min_value
	std::map<std::string, Endpoint> max_value;
	std::map<std::string, bool>     max_strict; //False if the max value can be exactly max_value

	for(auto iter1 = constraints.begin(); iter1 != constraints.end(); iter1++) {
		Endpoint constant = std::visit([](const auto &atomic_clock_constraint)
						-> Time { return atomic_clock_constraint.get_comparand(); },
						iter1->second); //Visit due to ClockConstraint being a variant

		std::optional<int> relation_opt = automata::get_relation_index(iter1->second);
		assert(relation_opt.has_value());
		int relation = relation_opt.value();

		auto l_val = max_value.find(iter1->first);
		auto l_strict = max_strict.find(iter1->first);
		auto g_val = min_value.find(iter1->first);
		auto g_strict = min_strict.find(iter1->first);

		switch (relation)
		{
		case 0: //less
			if(l_val == max_value.end()) {
				max_value.insert( {iter1->first, constant} );
				max_strict.insert( {iter1->first, true} );
			} else {
				if(!l_strict->second && l_val->second >= constant) {
					l_val->second = constant;
					l_strict->second = true;
				} else if(l_val->second > constant) {
					l_val->second = constant;
				}
			}
			break;
		case 1: //less_equal
			if(l_val == max_value.end()) {
				max_value.insert( {iter1->first, constant} );
				max_strict.insert( {iter1->first, false} );
			} else {
				if(l_val->second > constant) {
					l_val->second = constant;
					l_strict->second = false;
				}
			}
			break;
		case 2: //equal_to
			if(l_val == max_value.end()) {
				max_value.insert( {iter1->first, constant} );
				max_strict.insert( {iter1->first, false} );
			} else {
				if(l_val->second > constant) {
					l_val->second = constant;
					l_strict->second = false;
				}
			}

			if(g_val == min_value.end()) {
				min_value.insert( {iter1->first, constant} );
				min_strict.insert( {iter1->first, false} );
			} else {
				if(g_val->second < constant) {
					g_val->second = constant;
					g_strict->second = false;
				}
			}
			break;
		case 4: //greater_equal
			if(g_val == min_value.end()) {
				min_value.insert( {iter1->first, constant} );
				min_strict.insert( {iter1->first, false} );
			} else {
				if(g_val->second < constant) {
					g_val->second = constant;
					g_strict->second = false;
				}
			}
			break;
		case 5: //greater
			if(g_val == min_value.end()) {
				min_value.insert( {iter1->first, constant} );
				min_strict.insert( {iter1->first, true} );
			} else {
				if(!g_strict->second && g_val->second <= constant) {
					g_val->second = constant;
					g_strict->second = true;
				} else if(g_val->second < constant) {
					g_val->second = constant;
				}
			}
			break;
		default: //not_equal or other oopsie (We assume inequality constraints don't exist)
			assert(false);
			break;
		}
	}

	//TODO Kinda inefficient, as ALL constraints for a clock are iterated, instead of iterating only clocks. But this is also just for verification (for now)
	for(const auto &[clock, _] : constraints) {
		if(min_value.find(clock) != min_value.end() && max_value.find(clock) != max_value.end()) {
			if(min_strict.at(clock) || max_strict.at(clock)) {
				if(min_value.at(clock) >= max_value.at(clock)) {
					return false;
				}
			} else {
				if(min_value.at(clock) > max_value.at(clock)) {
					return false;
				}
			}
		}
	}

	return true;
}

std::ostream &
operator<<(std::ostream &os, const automata::ClockConstraint &constraint)
{
	std::visit([&os](auto &&c) { os << c; }, constraint);
	return os;
}

std::ostream &
operator<<(std::ostream                                                &os,
           const std::multimap<std::string, automata::ClockConstraint> &constraints)
{
	if (constraints.empty()) {
		os << u8"⊤";
		return os;
	}
	bool first = true;
	for (const auto &[clock, constraint] : constraints) {
		if (first) {
			first = false;
		} else {
			os << u8" ∧ ";
		}
		os << clock << " " << constraint;
	}
	return os;
}

} // namespace tacos::automata
