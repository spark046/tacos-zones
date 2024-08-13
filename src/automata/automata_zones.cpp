#include "automata/automata_zones.h"
#include "automata/automata_zones.hpp"

namespace tacos::zones {

	std::multimap<std::string, automata::ClockConstraint>
	get_fulfilled_clock_constraints(const std::multimap<std::string, automata::ClockConstraint> allConstraints, std::string clock, ClockValuation val) {
		if(allConstraints.empty()) {
			return {};
		}

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

	std::vector<automata::ClockConstraint> 
	get_clock_constraints_from_zone(const Zone_slice &zone, RegionIndex max_region_index)
	{
		Endpoint max_constant;
		if(max_region_index % 2 == 0) {
			max_constant = max_region_index / 2;
		} else {
			max_constant = (max_region_index + 1) / 2;
		}

		if(zone.lower_bound_ == zone.upper_bound_) {
			return {automata::AtomicClockConstraintT<std::equal_to<Time>>(zone.lower_bound_)};
		}

		std::vector<automata::ClockConstraint> ret;
		
		if(zone.lower_isOpen_) {
			ret.push_back(automata::AtomicClockConstraintT<std::greater<Time>>(zone.lower_bound_));
		} else {
			ret.push_back(automata::AtomicClockConstraintT<std::greater_equal<Time>>(zone.lower_bound_));
		}

		if(zone.upper_bound_ <= max_constant) {
			if(zone.upper_isOpen_) {
				ret.push_back(automata::AtomicClockConstraintT<std::less<Time>>(zone.upper_bound_));
			} else {
				ret.push_back(automata::AtomicClockConstraintT<std::less_equal<Time>>(zone.upper_bound_));
			}
		}

		return ret;
	}

	bool
	is_satisfied(const automata::ClockConstraint &constraint, const Zone_slice &zone)
	{
		//TODO IS THIS EVEN TRUE????
		//If the zone is empty (i.e. invalid interval), then it will satisfy all constraints
		if(zone.lower_bound_ > zone.upper_bound_ || (zone.lower_bound_ == zone.upper_bound_ && zone.lower_isOpen_ && zone.upper_isOpen_)) {
			return true;
		}

		Endpoint constant = std::visit([](const auto &atomic_clock_constraint)
					  -> Time { return atomic_clock_constraint.get_comparand(); },
					  constraint); //Visit due to ClockConstraint being a variant

		std::optional<int> relation_opt = automata::get_relation_index(constraint);
		assert(relation_opt.has_value());
		int relation = relation_opt.value();

		switch (relation)
		{
		case 0: //less
			return (zone.lower_bound_ < constant && (zone.upper_bound_ < constant || (zone.upper_bound_ == constant && zone.upper_isOpen_)));
		case 1: //less_equal
			return (zone.lower_bound_ <  constant ||
				  (zone.lower_bound_ == constant && !zone.lower_isOpen_)) &&
				   (zone.upper_bound_ <= constant);
		case 2: //equal_to
			return zone.lower_bound_ == constant && zone.upper_bound_ == constant && !zone.lower_isOpen_ && !zone.upper_isOpen_;
		case 4: //greater_equal
			return (zone.upper_bound_ >  constant ||
				  (zone.upper_bound_ == constant && !zone.upper_isOpen_)) &&
				  zone.lower_bound_ >= constant;
		case 5: //greater
			return zone.upper_bound_ > constant && (zone.lower_bound_ > constant || (zone.lower_bound_ == constant && zone.lower_isOpen_));
		default: //not_equal or other oopsie (We assume inequality constraints don't exist for zones)
			assert(false);
		}

		return false;
	}

	bool
	is_valid_zone(const Zone_slice &zone)
	{
		return  (zone.lower_bound_ <= zone.max_constant_) &&
				(zone.upper_bound_ <= zone.max_constant_);
	}

	std::ostream &
	operator<<(std::ostream &os, const zones::Zone_slice &zone_slice)
	{
		//Check whether it is empty set
		if(zone_slice.is_empty()) {
			os << u8"∅";

			return os;
		}

		std::string leftBracket = "[";
		std::string rightBracket = "]";
		if(zone_slice.lower_isOpen_)
		{
			leftBracket = "(";
		}
		if(zone_slice.upper_isOpen_)
		{
			rightBracket = ")";
		}

		//Also print the max_constant if we are equal it
		if(zone_slice.upper_bound_ == zone_slice.max_constant_ && !zone_slice.upper_isOpen_) {
			os << leftBracket << zone_slice.lower_bound_ << "; " << u8"∞/" << zone_slice.upper_bound_ << ")";
		} else if(zone_slice.upper_bound_ > zone_slice.max_constant_) { //Exceeding max_constant
			os << leftBracket << zone_slice.lower_bound_ << "; " << u8"∞/" << zone_slice.upper_bound_ << "/" << zone_slice.max_constant_ << ")";
		} else {
			os << leftBracket << zone_slice.lower_bound_ << "; " << zone_slice.upper_bound_ << rightBracket;
		}
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
