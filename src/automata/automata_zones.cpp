#include "automata/automata_zones.h"
#include "automata/automata_zones.hpp"

namespace tacos::zones {

	Zone_slice
	Zone_DBM::get_zone_slice(std::string clock) const
	{
		assert(graph_.has_clock(clock));

		if(!is_consistent()) {
			return Zone_slice{0, 0, true, true, max_constant_};
		}

		Zone_slice ret{0, 0, false, false, max_constant_};

		std::size_t index = graph_.get_index_of_clock(clock);

		const DBM_Entry &lower_bound = graph_.get_value(0, index);
		const DBM_Entry &upper_bound = graph_.get_value(index, 0);

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
		//assert((graph_.get(0,0) == DBM_Entry{0, true}));

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
		assert(graph_.has_clock(clock));

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

		//graph_.floyd_warshall();
	}

	bool
	Zone_DBM::is_consistent() const
	{
		return graph_.get_value(0, 0) == DBM_Entry{0, true};
	}

	//TODO This doesn't consider that old clocks may have been removed
	RegionIndex
	Zone_DBM::get_increment(Zone_DBM new_dbm) const
	{
		//Find the largest difference in magnitude, unless it is of a clock that has been reset.
		RegionIndex largest_difference = 0;

		for(const auto &clock : new_dbm.get_clocks()) {
			if(!has_clock(clock)) {
				continue;
			}
			std::size_t index = get_index_of_clock(clock);

			//I am stupid and don't know how to incorporate zero clock into for loop
			{
				RegionIndex lower_difference = new_dbm.graph_.get(clock, 0) - graph_.get_value(index, 0);
				RegionIndex upper_difference = new_dbm.graph_.get(0, clock) - graph_.get_value(0, index);
				RegionIndex difference = std::max(lower_difference, upper_difference);
				if(difference > largest_difference) {
					largest_difference = difference;
				}
			}

			for(const auto &other_clock : new_dbm.get_clocks()) {
				if(!has_clock(other_clock)) {
					continue;
				}

				std::size_t other_index = get_index_of_clock(other_clock);

				RegionIndex lower_difference = new_dbm.graph_.get(clock, other_clock) - graph_.get_value(index, other_index);
				RegionIndex upper_difference = new_dbm.graph_.get(other_clock, clock) - graph_.get_value(other_index, index);
				RegionIndex difference = std::max(lower_difference, upper_difference);
				if(difference > largest_difference) {
					largest_difference = difference;
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

	std::size_t
	Zone_DBM::get_index_of_clock(std::string clock) const
	{
		return graph_.get_index_of_clock(clock);
	}

	std::vector<std::string>
	Zone_DBM::get_clocks() const
	{
		return graph_.get_clocks();
	}

	bool
	Zone_DBM::add_clock(std::string clock_name)
	{
		return graph_.add_clock(clock_name);
	}

	bool
	Zone_DBM::copy_clock(std::string new_clock_name, std::string clock_to_copy)
	{
		//If same, then don't need to do anything
		if(new_clock_name == clock_to_copy) {
			return true;
		}

		if(!graph_.has_clock(clock_to_copy)) {
			return false;
		}

		if(!graph_.has_clock(new_clock_name)) {
			add_clock(new_clock_name);
		} else {
			graph_.unbound_clock(new_clock_name);
		}

		//Set the constraint new_clock - old_clock <= 0 AND old_clock - new_clock <= 0. This way the clocks are constrained to be the same
		graph_.get(new_clock_name, clock_to_copy) = DBM_Entry{0, true};
		graph_.get(clock_to_copy, new_clock_name) = DBM_Entry{0, true};

		//Make canonical to fill the entries of the new clock
		graph_.floyd_warshall();

		return true;
	}

	bool
	Zone_DBM::remove_clock(std::string clock_name)
	{
		return graph_.remove_clock(clock_name);
	}

	bool
	Zone_DBM::has_clock(std::string clock_name) const
	{
		return graph_.has_clock(clock_name);
	}

	Zone_DBM
	Zone_DBM::get_subset(std::set<std::string> clocks) const
	{
		Graph new_graph{clocks};

		for(const auto &clock : clocks) {
			new_graph.get(clock, 0) = at(clock, 0);
			new_graph.get(0, clock) = at(0, clock);

			//Get difference constraints too
			for(const auto &other_clock : clocks) {
				new_graph.get(clock, other_clock) = at(clock, other_clock);
			}
		}

		new_graph.floyd_warshall();

		Zone_DBM new_dbm{new_graph, max_constant_};
		return new_dbm;
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

	//~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
	// LOCAL FUNCTIONS FROM HERE ON
	//~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

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

	bool
	Graph::add_clock(std::string clock_name)
	{
		//Check whether clock already exists
		assert(!has_clock(clock_name));

		std::size_t old_size = size();
		Matrix new_matrix = Matrix(old_size + 1);

		//Copy the old matrix. New Rows and Columns are already unbounded, so no need to fill those in
		for(std::size_t i = 0; i < old_size; i++) {
			for(std::size_t j = 0; j < old_size; j++) {
				new_matrix(i, j) = get_value(i, j);
			}
		}

		//Update indices
		clock_to_index.push_back(clock_name);

		//Update Matrix
		matrix_ = new_matrix;

		//Get canonical form
		floyd_warshall();

		return true;
	}

	bool
	Graph::unbound_clock(std::string clock_name)
	{
		//Check whether clock exists
		if(!has_clock(clock_name)) {
			return false;
		}

		std::size_t index = get_index_of_clock(clock_name);

		for(std::size_t i = 0; i < size(); i++) {
			matrix_(i, index) = DBM_Entry{true, 0, false};
			matrix_(index, i) = DBM_Entry{true, 0, false};
		}

		floyd_warshall();

		return true;
	}

	bool
	Graph::remove_clock(std::string clock_name)
	{
		//Check whether clock exists
		assert(has_clock(clock_name));

		std::size_t index_to_delete = get_index_of_clock(clock_name);

		std::size_t old_size = size();
		Matrix new_matrix = Matrix(old_size);

		//Copy the old matrix up to the deleted clock
		for(std::size_t i = 0; i < index_to_delete; i++) {
			//Fill in top left corner
			for(std::size_t j = 0; j < index_to_delete; j++) {
				new_matrix(i, j) = matrix_.get(i, j);
			}

			//Fill in Top right and bottom left corner
			for(std::size_t j = index_to_delete + 1; j < old_size; j++) {
				new_matrix(i, j - 1) = matrix_.get(i, j);
				new_matrix(j - 1, i) = matrix_.get(j, i);
			}
		}

		//Fill in bottom right corner
		for(std::size_t i = index_to_delete + 1; i < old_size; i++) {
			for(std::size_t j = index_to_delete + 1; j < old_size; j++) {
				new_matrix(i-1, j-1) = matrix_.get(i,j);
			}
		}

		//Update Indices (Addition is for having an iterator)
		clock_to_index.erase(clock_to_index.begin() + index_to_delete);

		//Update Matrix
		matrix_ = new_matrix;

		//Make canonical
		floyd_warshall();

		return true;
	}

	std::vector<std::string> Graph::get_clocks() const
	{
		std::vector<std::string> ret;
		for(std::size_t i = 1; i < size(); i++) {
			ret.push_back(clock_to_index[i]);
		}

		return ret;
	}

	bool
	Graph::has_clock(std::string clock_name) const
	{
		return std::find(clock_to_index.begin(), clock_to_index.end(), clock_name) != clock_to_index.end();
	}

	RegionIndex
	DBM_Entry::operator-(const DBM_Entry &s2) const
	{
		if(infinity_ || s2.infinity_) {
			return 0;
		}

		RegionIndex result = 0; //Signed integer since negative numbers will be involved in calculation
		
		//1. Calculate fractional parts of LHS and RHS
		//(e.g. < -1 means > 1, so fractional part is: +0.1, while < 1 means fractional part is: -0.1, and for <= fractional part is always 0)
		int fractional_lhs = 0;
		if(!non_strict_) {
			if(value_ < 0) {
				fractional_lhs = 1;
			} else {
				fractional_lhs = -1;
			}
		}

		int fractional_rhs = 0;
		if(!s2.non_strict_) {
			if(s2.value_ < 0) {
				fractional_rhs = 1;
			} else {
				fractional_rhs = -1;
			}
		}

		//2. Calculate integer difference
		if(s2.value_ > value_) {
			result = (RegionIndex) 2*(s2.value_ - value_);
		} else {
			result = (RegionIndex) 2*(value_ - s2.value_);
		}

		//3. Apply fractional part difference
		if(fractional_lhs != fractional_rhs) { //If both fractional parts are the same, they cancel each other out
			if(fractional_lhs == 0 || fractional_rhs == 0) { //If one fractional part is 0, then we just go from an integer region to a fractional region
				result += 1;
			} else { //We have a combination of +1 and -1, so difference is 2 regions, as we go from fractional to integer back to fractional
				result += 2;
			}
		}

		return result;
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
	get_clock_constraints_from_zone(const Zone_slice &zone, RegionIndex max_constant)
	{
		if(zone.is_empty()) {
			return {};
		}
		
		if(zone.lower_bound_ == zone.upper_bound_ && !zone.lower_isOpen_ && !zone.upper_isOpen_) {
			return {automata::AtomicClockConstraintT<std::equal_to<Time>>(zone.lower_bound_)};
		}

		std::vector<automata::ClockConstraint> ret;
		
		if(zone.lower_isOpen_) {
			ret.push_back(automata::AtomicClockConstraintT<std::greater<Time>>(zone.lower_bound_));
		} else {
			ret.push_back(automata::AtomicClockConstraintT<std::greater_equal<Time>>(zone.lower_bound_));
		}

		if(zone.upper_bound_ < max_constant) {
			if(zone.upper_isOpen_) {
				ret.push_back(automata::AtomicClockConstraintT<std::less<Time>>(zone.upper_bound_));
			} else if(zone.upper_bound_ < max_constant) {
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
		std::vector<std::string> clocks = dbm.get_clocks();

		for (std::size_t i = 0; i < dbm.size() + 1; i++)
		{
			os << "| ";
			for (std::size_t j = 0; j < dbm.size() + 1; j++)
			{
				os << dbm.at(i, j) << " ";
			}
			if(i == 0) {
				os << "| 0\n";
			} else {
				os << "| " << clocks.at(i-1) << "\n";
			}
			
		}

		return os;
	}

} // namespace tacos::automata
