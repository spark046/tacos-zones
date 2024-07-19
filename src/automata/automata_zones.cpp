#include "automata/automata_zones.h"
#include "automata/automata_zones.hpp"

namespace tacos::zones {

	std::multimap<std::string, automata::ClockConstraint>
	get_fulfilled_clock_constraints(const std::multimap<std::string, automata::ClockConstraint> allConstraints, std::string clock, ClockValuation val) {
		std::multimap<std::string, automata::ClockConstraint> ret = {};

		for(auto it1 = allConstraints.begin(); it1 != allConstraints.end(); it1++) {
			if(it1->first == clock) {
				if(automata::is_satisfied(it1->second, val)) {
					ret.insert(*it1);
				}
			}
		}

		return ret;
	}

	RegionIndex
	get_clock_constraints(ClockValuation timePoint) {
		return timePoint;
	}

	std::ostream &
	operator<<(std::ostream &os, const zones::Zone_slice &zone_slice)
	{
		std::string leftBracket = "[";
		std::string rightBracket = "]";
		if(zone_slice.lower_isStrict_)
		{
			leftBracket = "(";
		}
		if(zone_slice.upper_isStrict_)
		{
			rightBracket = ")";
		}

		os << leftBracket << zone_slice.lower_bound_ << "; " << zone_slice.upper_bound_ << rightBracket;
		return os;
	}

	std::ostream &
	operator<<(std::ostream &os, const std::map<std::string, tacos::zones::Zone_slice> &zone)
	{
		if(zone.empty()) {
			os << "{}";
			return os;
		}

		os << "{ ";

		bool first = true;

		for(const auto &[clock, slice] : zone)
		{
			if(first) {
				first = false;
			} else {
				os << ", ";
			}
			os << slice << "_" << clock;
		}

		os << " }";

		return os;
	}

} // namespace tacos::automata
