#include "automata/automata_zones.h"
#include "automata/automata_zones.hpp"

namespace tacos::zones {

	Zone_slice
	Zone_DBM::get_zone_slice(std::string clock)
	{
		if(!is_consistent()) {
			return Zone_slice{0, 0, true, true, max_constant_};
		}

		Zone_slice ret{0, 0, false, false, max_constant_};

		const DBM_Entry &lower_bound = graph_.get(0, clock);
		const DBM_Entry &upper_bound = graph_.get(clock, 0);

		if(lower_bound.value_ < 0) {
			ret.lower_bound_ = (Endpoint) -lower_bound.value_;
		} else {
			ret.lower_bound_ = 0;
		}
		
		ret.lower_isOpen_ = !lower_bound.non_strict_;

		ret.upper_bound_ = (Endpoint) upper_bound.value_;
		ret.upper_isOpen_ = !upper_bound.non_strict_;

		if(lower_bound.infinity_) {
			ret.lower_bound_ = 0;
			ret.lower_isOpen_ = false;
		}

		if(ret.lower_bound_ > max_constant_) {
			ret.lower_bound_ = max_constant_;
			ret.lower_isOpen_ = false;
		}

		if(upper_bound.infinity_ || ret.upper_bound_ > max_constant_) {
			ret.upper_bound_ = max_constant_;
			ret.upper_isOpen_ = false;
		}

		assert(is_valid_zone(ret));

		return ret;
	}

	void
	Zone_DBM::delay()
	{
		for(std::size_t i = 1; i < graph_.size(); i++) {
			graph_.get(i, 0).infinity_ = true;
		}
	}

	void
	Zone_DBM::reset(std::string clock)
	{
		std::size_t index = graph_.get_index_of_clock(clock);

		for(std::size_t i = 0; i < graph_.size(); i++) {
			graph_.get(index, i) = DBM_Entry{0, true} + graph_.get(0, i);
			graph_.get(i, index) = graph_.get(i, 0) + DBM_Entry{0, true};
		}

		normalize();
	}

	void
	Zone_DBM::conjunct(std::string clock, automata::ClockConstraint clock_constraint)
	{
		std::size_t index = graph_.get_index_of_clock(clock);

		DBM_Entry lower_entry{true, 0, false};
		DBM_Entry upper_entry{true, 0, false};

		int constant = (int) std::visit([](const auto &atomic_clock_constraint)
						-> Time { return atomic_clock_constraint.get_comparand(); },
						clock_constraint); //Visit due to ClockConstraint being a variant

		std::optional<int> relation_opt = automata::get_relation_index(clock_constraint);
		assert(relation_opt.has_value());
		int relation = relation_opt.value();

		switch (relation)
		{
		case 0: //less
			upper_entry.infinity_ = false;
			upper_entry.value_ = constant;
			upper_entry.non_strict_ = false;
			break;
		case 1: //less_equal
			upper_entry.infinity_ = false;
			upper_entry.value_ = constant;
			upper_entry.non_strict_ = true;
			break;
		case 2: //equal_to
			upper_entry.infinity_ = false;
			upper_entry.value_ = constant;
			upper_entry.non_strict_ = true;

			lower_entry.infinity_ = false;
			lower_entry.value_ = -constant;
			lower_entry.non_strict_ = true;
			break;
		case 4: //greater_equal
			lower_entry.infinity_ = false;
			lower_entry.value_ = -constant;
			lower_entry.non_strict_ = true;
			break;
		case 5: //greater
			lower_entry.infinity_ = false;
			lower_entry.value_ = -constant;
			lower_entry.non_strict_ = false;
			break;
		default: //not_equal or other oopsie (We assume inequality constraints don't exist for zones)
			assert(false);
			break;
		}

		//Apply the algorithm on lower_entry and also upper_entry
		if(!upper_entry.infinity_) {
			and_func(index, 0, upper_entry);
		}

		if(!lower_entry.infinity_) {
			and_func(0, index, lower_entry);
		}


		normalize();
	}

	void
	Zone_DBM::conjunct(std::multimap<std::string, automata::ClockConstraint> clock_constraints) {
		for(auto iter1 = clock_constraints.begin(); iter1 != clock_constraints.end(); iter1++) {
			conjunct(iter1->first, iter1->second);
		}
	}

	void
	Zone_DBM::normalize()
	{
		for(std::size_t i = 0; i < graph_.size(); i++) {
			for(std::size_t j = 0; j < graph_.size(); j++) {
				if(!graph_.get(i, j).infinity_ && DBM_Entry{(int) max_constant_, true} < graph_.get(i, j)) {
					graph_.get(i, j).infinity_ = true;
				} else if(!graph_.get(i, j).infinity_ && graph_.get(i, j) < DBM_Entry{-1*((int) max_constant_), false}) {
					graph_.get(i, j) = DBM_Entry{-1*((int) max_constant_), false};
				}
			}
		}

		graph_.floyd_warshall();
	}

	bool
	Zone_DBM::is_consistent()
	{
		return graph_.get(0, 0).value_ == 0;
	}

	RegionIndex
	Zone_DBM::get_increment(Zone_DBM new_dbm) const
	{
		//Find the largest difference in magnitude, unless it is of a clock that has been reset.
		RegionIndex largest_difference = 0;

		for(std::size_t i = 0; i < graph_.size(); i++) {
			for(std::size_t j = 0; j < graph_.size(); j++) {
				RegionIndex difference = new_dbm.graph_.get(i, j) - graph_.get_value(i, j);
				if(difference != 0 && graph_.get_value(i, j) != DBM_Entry{0, true}) {
					if(difference > largest_difference) {
						largest_difference = difference;
					}
				}
			}
		}

		return largest_difference;
	}

	void
	Zone_DBM::and_func(std::size_t x, std::size_t y, DBM_Entry comparison)
	{
		//Check whether this will make the zone inconsistent, i.e. negative cycle
		if(graph_.get(y, x) + comparison < DBM_Entry{0, false}) {
			graph_.get(0, 0) = DBM_Entry{-1, false};
			return;
		}

		if(comparison < graph_.get(x, y)) {
			graph_.get(x, y) = comparison;
			
			//Make canonical by getting shortest paths
			graph_.floyd_warshall();
		}
	}

	DBM_Entry
	Zone_DBM::at(std::size_t x, std::size_t y) const
	{
		return graph_.get_value(x, y);
	}

	DBM_Entry
	Zone_DBM::at(std::string clock, std::size_t y) const
	{
		return graph_.get_value(graph_.get_index_of_clock(clock), y);
	}

	DBM_Entry
	Zone_DBM::at(std::size_t x, std::string clock) const
	{
		return graph_.get_value(x, graph_.get_index_of_clock(clock));
	}

	DBM_Entry
	Zone_DBM::at(std::string clock1, std::string clock2) const
	{
		return graph_.get_value(graph_.get_index_of_clock(clock1), graph_.get_index_of_clock(clock2));
	}

	std::size_t
	Zone_DBM::size() const
	{
		return graph_.size() - 1;
	}

	void 
	Graph::floyd_warshall()
	{
		//Inconsistent DBMs can't become canonical
		if(get(0,0).value_ != 0) {
			return;
		}

		//copied from Wikipedia

		std::size_t n = size();

		//Set distance of a node to itself to 0
		for(std::size_t u = 0; u < n; u++) {
			get(u, u) = DBM_Entry{0, true};
		}

		//Find shortest distance between each pair of nodes
		for(std::size_t k = 0; k < n; k++) {
			for(std::size_t i = 0; i < n; i++) {
				for(std::size_t j = 0; j < n; j++) {
					DBM_Entry new_distance = get(i, k) + get(k, j);

					if(new_distance < get(i, j)) {
						get(i, j) = new_distance;
					}
				}
			}
		}
	}

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

	std::ostream &
	operator<<(std::ostream &os, const tacos::zones::DBM_Entry &dbm_entry)
	{
		if(dbm_entry.infinity_) {
			os << u8"∞";
			return os;
		}

		std::string relation;
		if(dbm_entry.non_strict_) {
			relation = u8"≤";
		} else {
			relation = "<";
		}

		os << "(" << dbm_entry.value_ << ", " << relation << ")";

		return os;
	}

	std::ostream &
	operator<<(std::ostream &os, const tacos::zones::Zone_DBM &dbm)
	{
		for (std::size_t i = 0; i < dbm.size() + 1; i++)
		{
			os << "| ";
			for (std::size_t j = 0; j < dbm.size() + 1; j++)
			{
				os << dbm.at(i, j) << " ";
			}
			os << "|\n";
		}

		return os;
	}

} // namespace tacos::automata
