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

	/** Entry within the Adjacency Matrix, i.e. this is the type for the edge weights */
	struct DBM_Entry
	{
		bool infinity_; //Whether this entry is supposed to be infinity. If this is true, the rest is essentially ignored
		int value_; //Value. Unlike Endpoints this can be positive or negative
		bool non_strict_; //i.e. true means <=, while false means <

		DBM_Entry(bool infty, int value, bool non_strict) : 
		infinity_(infty), value_(value), non_strict_(non_strict)
		{
			// :)
		}

		DBM_Entry(int value, bool non_strict) : 
		infinity_(false), value_(value), non_strict_(non_strict)
		{
			// :)
		}

		/** Adds another Entry to this entry 
		 * 
		 * Adding infinity will always result in infinity.
		 * Otherwise the values are added together normally.
		 * 
		 * Strictness is added like:
		 * <= + <= is <=
		 * <= + <  is <
		 * < + <=  is <
		 * < + <   is <
		*/
		DBM_Entry
		operator+(const DBM_Entry &s2) const
		{
			DBM_Entry result{infinity_, value_, non_strict_};

			result.infinity_ |= s2.infinity_;
			result.value_ += s2.value_;
			result.non_strict_ = result.non_strict_ && s2.non_strict_;

			return result;
		}

		/** Finds the magnitude of the difference between two entries in the form of a RegionIndex
		 * (i.e. the result which might have fractional part is regionalized)
		 * 
		 * Subtracting (from) infinity means that something is unbounded, which doesn't need any increment.
		 * 
		 * Strictness is subtracted like:
		 * <= - <= is 0
		 * <= - <  is -1
		 * < + <=  is 1
		 * < + <   is 0
		 * 
		 * If RHS's value was negative, then fractional part is inverted as it was a greater(-equal) constraint
		 * Similarily if result was negative, fractional part is inverted as the direction is inverted too (to retain positive result)
		*/
		RegionIndex
		operator-(const DBM_Entry &s2) const
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

		/** Compare two DBM Entries.
		 * 
		 * 1. Compare values as normal
		 * 2. If values are the same, then compare non_strict as 0 or 1, as < is smaller than <=
		 * 
		 * @param s1 The first entry
		 * @param s2 The second entry
		 * @return true if s1 is lexicographically smaller than s2.
		 */
		friend bool
		operator<(const DBM_Entry &s1, const DBM_Entry &s2) //Use forward_as_tuple instead of tie due to rvalues
		{
			//Infinity can never be smaller than something
			if(s1.infinity_) {
				return false;
			} else if(s2.infinity_) { //Everything other than infinity must be smaller
				return true;
			}

			return std::forward_as_tuple(s1.value_, s1.non_strict_)
				< std::forward_as_tuple(s2.value_, s2.non_strict_);
		}

		/** Check two DBM Entries for equality.
		 * @param s1 The first entry
		 * @param s2 The second entry
		 * @return true if s1 is equal to s2
		 */
		friend bool
		operator==(const DBM_Entry &s1, const DBM_Entry &s2) {
			return !(s1 < s2) && !(s2 < s1);
		}

		/** Check two DBM Entries for inequality.
		 * @param s1 The first entry
		 * @param s2 The second entry
		 * @return true if s1 is not equal to s2
		 */
		friend bool
		operator!=(const DBM_Entry &s1, const DBM_Entry &s2) {
			return !(s1 == s2);
		}
	};

	/** Class for a weighted graph modelled as an Adjacency Matrix
	 * 
	 * Vertexes are clock names together with an extra vertex for the zero clock
	 * Edge weights are DBM_Entries
	 */
	class Graph
	{
		public:
		/** Default Constructor with no clocks so also an empty Matrix */
		Graph()
		{

		}

		/** Constructs a new Graph for this set of clocks. Each edge is labeled with infinity */
		Graph(std::set<std::string> clocks) {
			//Assign each clock an index:
			int k = 1;
			for(const auto &clock : clocks) {
				clock_to_index[clock] = k;
				k++;
			}

			matrix_ = Matrix(k);
		}

		public:
		/** Calculate shortest path from each vertex to each vertex and update the matrix accordingly */
		void floyd_warshall();

		/** Returns size of graph. The size is the amount of clocks including the implicit zero clock*/
		std::size_t
		size() const
		{
			return matrix_.size();
		}

		/** Get the index as which */
		std::size_t
		get_index_of_clock(std::string clock) const
		{
			return clock_to_index.at(clock);
		}

		/** Get the DBM_Entry at these indices */
		DBM_Entry& get(std::size_t x, std::size_t y)
		{
			return matrix_(x, y);
		}

		/** Get the DBM_Entry of these clocks */
		DBM_Entry& get(std::string clock1, std::string clock2)
		{
			return matrix_(clock_to_index[clock1], clock_to_index[clock2]);
		}

		/** Get the DBM_Entry of this index and clock */
		DBM_Entry& get(std::size_t x, std::string clock)
		{
			return matrix_(x, clock_to_index[clock]);
		}

		/** Get the DBM_Entry of this clock and index */
		DBM_Entry& get(std::string clock, std::size_t y)
		{
			return matrix_(clock_to_index[clock], y);
		}

		/** Get the DBM_Entry as a value at these indices (For constness, mostly testing) */
		DBM_Entry get_value(std::size_t x, std::size_t y) const
		{
			return matrix_.get(x, y);
		}

		private:
		//~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~HELPING MATRIX~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
		/** Class of Matrix in which the graph is stored */
		class Matrix
		{
			public:
			/** Default Constructor with empty vector */
			Matrix()
			{

			}

			Matrix(std::size_t size)
			{
				m_.resize(size, std::vector<DBM_Entry>(size, DBM_Entry{true, 0, false}));
			}

			DBM_Entry& operator()(std::size_t x, std::size_t y)
			{
				return m_.at(x).at(y);
			}

			DBM_Entry get(std::size_t x, std::size_t y) const
			{
				return m_.at(x).at(y);
			}

			/** Returns the size of this matrix */
			std::size_t
			size() const
			{
				return m_.size();
			}

			private:
			std::vector<std::vector<DBM_Entry>> m_;
		};

		//~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~END MATRIX~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

		private:
		Matrix matrix_;
		std::map<std::string, std::size_t> clock_to_index;
	};

	/** Class for storing zones as a Difference Bound Matrix
	 * 
	 * This allows for the easy storing of differences between clocks, while also ensuring they stay consistent.
	 * 
	 * This class is an implementation following the pseudocode algorithms presented in:
	 * 
	 * Bengtsson, J., & Yi, W. (2003, September). Timed automata: Semantics, algorithms and tools.
	 * In Advanced Course on Petri Nets (pp. 87-124). Berlin, Heidelberg: Springer Berlin Heidelberg.
	 */
	class Zone_DBM
	{
		public:
		/** Default Constructor creating an empty DBM. Used when zones aren't needed.
		 * 
		 * TODO This might end up wasting space when using the region construction, but should be negligablesd
		 */
		Zone_DBM()
		{

		}

		/** Construct the initial Zone Difference Bound Matrix (DBM) for the given clocks.
		 * This will be a graph with |clocks|+1 many vertices.
		 * Nothing is bounded in the beginning, i.e. everything is bounded by only infinity.
		 * 
		 * @param clocks The set of all clocks that will be covered by this zone
		 * @param max_constant The maximal constant that can appear for any given clock
		 */
		Zone_DBM(std::set<std::string> clocks, Endpoint max_constant) : max_constant_(max_constant) {
			graph_ = Graph(clocks);
		}

		/** Construct the initial Zone Difference Bound Matrix (DBM) for the given clock constraints.
		 * This will be a graph with |clocks|+1 many vertices.
		 * 
		 * @param clock_constraints The multimap of all clock constraints that will be covered by this zone. This must also contain all possible clocks
		 * @param max_constant The maximal constant that can appear for any given clock
		 */
		Zone_DBM(std::multimap<std::string, automata::ClockConstraint> clock_constraints, Endpoint max_constant) : max_constant_(max_constant) {
			std::set<std::string> clocks; // set of all clocks

			//TODO This is done naively due to me not having time T.T
			for(auto iter1 = clock_constraints.begin(); iter1 != clock_constraints.end(); iter1++)
			{
				clocks.insert(iter1->first);
			}

			graph_ = Graph(clocks);

			conjunct(clock_constraints);
		}

		/** Get the Zone_slice of this clock */
		Zone_slice get_zone_slice(std::string clock);

		/** Delays a DBM. Every Entry at graph_.get(i, 0) is set to infinity */
		void delay();

		/** Resets a clock back to zero. The canonical form is preserved
		 * 
		 * @param clock The clock to reset to zero
		 */
		void reset(std::string clock);

		/** Conjuncts this DBM with a clock constraint
		 * 
		 * If the DBM stops being in canonical form because of this, it is put back in line as well.
		 * 
		 * @param constraint The clock constraint to change the DBM with
		 */
		void conjunct(std::string clock, automata::ClockConstraint constraint);

		/** Conjuncts this DBM with a multimap of clock constraints
		 * 
		 * If the DBM stops being in canonical form because of this, it is put back in line as well.
		 * 
		 * @param clock_constraints The clock constraints to change the DBM with
		 */
		void conjunct(std::multimap<std::string, automata::ClockConstraint> clock_constraints);

		/** Normalize this DBM according to max_constant_ */
		void normalize();

		/** Check whether this zone is consistent, i.e. it has no empty sets.
		 * 
		 * This is accomplished by always marking inconsistent DBMs with a negative value at D_00
		 */
		bool is_consistent();

		/** For testing */
		std::map<std::string, std::size_t>
		get_indexes(std::set<std::string> clocks)
		{
			std::map<std::string, std::size_t> ret;

			for(const auto &clock : clocks) {
				ret.insert( {clock, graph_.get_index_of_clock(clock)} );
			}

			return ret;
		}

		/** Gets graph element at x,y
		 */
		DBM_Entry at(std::size_t x, std::size_t y) const;

		/** Gets graph element at index(clock),y
		 */
		DBM_Entry at(std::string clock, std::size_t y) const;

		/** Gets graph element at x,index(clock)
		 */
		DBM_Entry at(std::size_t x, std::string clock) const;

		/** Gets graph element at index(clock),index(clock)
		 */
		DBM_Entry at(std::string clock1, std::string clock2) const;

		/** Calculates the increment needed in order to reach the new DBM.
		 * 
		 * @param new_dbm The new DBM that is supposed to be reached
		 * @return The needed increment as a Region Index
		 */
		RegionIndex get_increment(Zone_DBM new_dbm) const;

		/** Returns the amount of clocks in this DBM (excluding 0) */
		std::size_t size() const;

		private:
		/** Conjuncts the DBM with this diagonal clock constraint: comparison(x,y)
		 * 
		 * e.g. if comparison is (2, <=), then the clock constraint is:
		 * x - y <= 2
		 * 
		 * TODO Use the actual algorithm provided by Bengtsson and Yi, instead of the text description, as that is supposed
		 * to be O(n^2) instead of O(n^3)
		 * 
		 * @param x index of first clock
		 * @param y index of second clock
		 * @param comparison DBM_Entry denoting the constant and type of the comparison
		 */
		void and_func(std::size_t x, std::size_t y, DBM_Entry comparison);

		public:
		//Max constant that may appear in any zone
		Endpoint max_constant_;

		private:
		Graph graph_;
	};

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
	get_fulfilled_clock_constraints(
		const std::multimap<std::string, automata::ClockConstraint> allConstraints,
		std::string clock, ClockValuation val);

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

	std::ostream &
	operator<<(std::ostream &os, const zones::Zone_slice &zone_slice);

	std::ostream &
	operator<<(std::ostream &os, const std::map<std::string, tacos::zones::Zone_slice> &zone);

	std::ostream &
	operator<<(std::ostream &os, const zones::DBM_Entry &dbm_entry);

	std::ostream &
	operator<<(std::ostream &os, const zones::Zone_DBM &dbm);

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

template <>
struct formatter<tacos::zones::DBM_Entry> : ostream_formatter
{
};

template <>
struct formatter<tacos::zones::Graph> : ostream_formatter
{
};

} //fmt

#include "automata_zones.hpp"

#endif