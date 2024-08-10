#pragma once

#include "automata/ata.h"
// TODO Regions should not be TA-specific
#include "automata/automata_zones.h"
#include "automata/ta_regions.h"
#include "mtl/MTLFormula.h"
#include "utilities/numbers.h"
#include "utilities/types.h"

#include <fmt/ostream.h>
#include <float.h>

//There were some bugs, probably related to overflows
#define ZONE_INFTY 30000

/** Represents symbolic states used for Canonical Words */
namespace tacos::search {

/** Always use ATA configurations over MTLFormulas */
template <typename ConstraintSymbolType>
using ATAConfiguration = automata::ata::Configuration<logic::MTLFormula<ConstraintSymbolType>>;

/** @brief The state of a plant
 *
 * An expanded state (location, clock_name, clock_valuation) of a plant.
 * A plant may be a TA or a Golog Program, depending on the template argument. */
template <typename LocationT>
struct PlantState
{
	/** The location part of this state */
	LocationT location;
	/** The clock name of this state */
	std::string clock;
	/** The clock valuation of the clock in this state */
	ClockValuation clock_valuation;
};

/** Compare two PlantStates
 * @param s1 The first state
 * @param s2 The second state
 * @return true if s1 is lexicographically smaller than s2
 */
template <typename LocationT>
bool
operator<(const PlantState<LocationT> &s1, const PlantState<LocationT> &s2)
{
	return std::tie(s1.location, s1.clock, s1.clock_valuation)
	       < std::tie(s2.location, s2.clock, s2.clock_valuation);
}

/** Always use ATA states over MTLFormulas */
template <typename ConstraintSymbolType>
using ATAState = automata::ata::State<logic::MTLFormula<ConstraintSymbolType>>;

/**
 * An abstract struct for a symbolic state for either a Plant or an ATA.
 * 
 * A symbolic state always has a location and a symbolic representation of the current valuation.
 * Optionally the name for a specific clock may also exist.
 * 
 * This is templated to allow for any kinds of locations just like with non-symbolic states.
 * More importantly a template for the type of symbolic representation, e.g. regions or zones is available.
 * 
 * @tparam LocationType How the locations are encoded
 * @tparam SymbolicRepresentationType The type of symbolic representation used. For regions it is a RegionIndex (int), while for zones it is a multimap consisting of a clock's name and a corresponding clock constraint
 */
template<typename LocationType, typename SymbolicRepresentationType>
struct SymbolicState
{
protected:
	/**
	 * Increments a state by one time step
	 * 
	 * @param max_region_index The maximal constant that should not be exceeded represented as a RegionIndex
	 */
	virtual void virt_increment_valuation(RegionIndex max_region_index) = 0;

public:
	LocationType location;

	std::string clock;

	SymbolicRepresentationType symbolic_valuation;

	SymbolicState(LocationType location_p, std::string clock_p, SymbolicRepresentationType symbolic_valuation_p) : 
	location(location_p), clock(clock_p), symbolic_valuation(symbolic_valuation_p)
	{
		
	}

	/**
	 * Increments a state by one time step.
	 * Regions are just incremented by one, while zones are delayed
	 * 
	 * @param max_region_index The maximal constant that should not be exceeded represented as a RegionIndex. Default is ZONE_INFTY (30000)
	 */
	void increment_valuation(RegionIndex max_region_index = ZONE_INFTY)
	{
		virt_increment_valuation(max_region_index);
	}

	/** Compare two symbolic states.
	 * @param s1 The first state
	 * @param s2 The second state
	 * @return true if s1 is lexicographically smaller than s2
	 */
	friend bool
	operator<(const SymbolicState<LocationType, SymbolicRepresentationType> &s1, const SymbolicState<LocationType, SymbolicRepresentationType> &s2)
	{
		return std::tie(s1.location, s1.clock, s1.symbolic_valuation)
		       < std::tie(s2.location, s2.clock, s2.symbolic_valuation);
	}

	/** Check two symbolic states for equality.
	 * Two symbolic states are considered equal if they have the same location(, clock name), and
	 * symbolic time.
	 * @param s1 The first state
	 * @param s2 The second state
	 * @return true if s1 is equal to s2
	 */
	friend bool
	operator==(const SymbolicState<LocationType, SymbolicRepresentationType> &s1, const SymbolicState<LocationType, SymbolicRepresentationType> &s2) {
		return !(s1 < s2) && !(s2 < s1);
	}
};

/** A regionalized plant state.
 *
 * A PlantRegionState is a tuple (location, clock_name, clock_region)
 */
template <typename LocationT>
struct PlantRegionState : public SymbolicState<LocationT, RegionIndex>
{
	//saves a mouthful
	using Base = SymbolicState<LocationT, RegionIndex>;

	PlantRegionState(LocationT location_p, std::string clock_p, RegionIndex region_index_p) : 
	Base::SymbolicState(location_p, clock_p, region_index_p)
	{
		//Nothing here...
	}


	void virt_increment_valuation(RegionIndex max_region_index)
	{
		if(Base::symbolic_valuation < max_region_index) {
			Base::symbolic_valuation += 1;
		}
	}
};

/** A regionalized ATA state.
 *
 * An ATARegionState is a pair (location, clock_region) */
template <typename ConstraintSymbolType>
struct ATARegionState : public SymbolicState<logic::MTLFormula<ConstraintSymbolType>, RegionIndex>
{
	using Base = SymbolicState<logic::MTLFormula<ConstraintSymbolType>, RegionIndex>;

	//We have only one clock, so the clock of SymbolicState is left empty
	ATARegionState(logic::MTLFormula<ConstraintSymbolType> formula, RegionIndex valuation) : 
	Base::SymbolicState(formula, "", valuation)
	{
		//Nothing here...
	}

	void virt_increment_valuation(RegionIndex max_region_index)
	{
		if(Base::symbolic_valuation < max_region_index) {
			Base::symbolic_valuation += 1;
		}
	}
};

/** A zone state that can be for either a Plant or an ATA.
 *
 * A ZoneState is a tuple (location, clock_name, set of clock constraints)
 * (This is effectively a PlantZoneState, but is kept seperate to preserve proper inheritance relations with ATAZoneState)
 */
template <typename LocationType>
struct ZoneState : public SymbolicState<LocationType, zones::Zone_slice>
{
	//saving a mouthful
	using ZoneSlice = zones::Zone_slice;
	//saving a second mouthful
	using Base = SymbolicState<LocationType, ZoneSlice>;

	ZoneState(LocationType location_p, std::string clock_p, ZoneSlice zone_p) : 
	Base::SymbolicState(location_p, clock_p, zone_p)
	{

	}

	/** Overloaded Constructor allowing the use of a set of ClockConstraints to initialize a ZoneState */
	ZoneState(LocationType location_p, std::string clock_p, std::multimap<std::string, automata::ClockConstraint> clock_constraint, Endpoint max_constant) :
	Base::SymbolicState(location_p, clock_p, [&clock_constraint, &clock_p, &max_constant](){
		ZoneSlice ret = ZoneSlice(0, ZONE_INFTY, false, false, max_constant);

		if(max_constant > 0) {
			ret.upper_bound_ = max_constant;
		}

		if(clock_constraint.empty()) {
			return ret;
		}

		ret.conjunct(clock_constraint, clock_p);
		
		return ret;
	}())
	{

	}

	/**
	 * Delays a zone by incrementing all clock valuations by any arbitrary amount.
	 * 
	 * In particular, this means all zones upper bounds are stretched to infinity.
	 * This means they are set to the maximal constant.
	 * 
	 * If the previous maximal constant is smaller than the parameter given, then the maximal constant is also updated.
	 */
	void virt_increment_valuation(RegionIndex max_region_index)
	{
		ZoneSlice &zone = Base::symbolic_valuation;

		//If max_region_index is 0, then K is too to avoid integer underflow.
		//Inverse from search::get_time_successor, not sure why it is done like this instead of checking whether it's even, etc.
		Endpoint K = max_region_index == 0 ? 0 : (max_region_index - 1) / 2;

		//If even the lower bound is larger than the max constant, something is pretty wrong
		assert(K == 0 || zone.lower_bound_ <= K);

		//We take/keep the larger of the two maximal constants 
		if(zone.max_constant_ >= K) {
			zone.upper_bound_ = zone.max_constant_;
			zone.upper_isOpen_ = false;
		} else {
			zone.upper_bound_ = K;
			zone.upper_isOpen_ = false;
			zone.max_constant_ = K;
		}
	}

	/** Compare two zone states.
	 * 
	 * @param s1 The first state
	 * @param s2 The second state
	 * @return true if s1 is lexicographically smaller than s2
	 */
	friend bool
	operator<(const ZoneState<LocationType> &s1, const ZoneState<LocationType> &s2)
	{
		return std::tie(s1.location, s1.clock, s1.symbolic_valuation)
		       < std::tie(s2.location, s2.clock, s2.symbolic_valuation);
	}
	
	/** Check two zone states for equality.
	 * Two symbolic states are considered equal if they have the same location(, clock name), and
	 * symbolic time.
	 * 
	 * @param s1 The first state
	 * @param s2 The second state
	 * @return true if s1 is equal to s2
	 */
	friend bool
	operator==(const ZoneState<LocationType> &s1, const ZoneState<LocationType> &s2) {
		return !(s1 < s2) && !(s2 < s1);
	}

};

/**
 * The zone state of a Plant state
 * 
 * A PlantZoneState is a triple (location, clock_name, set of clock constraints)
 */
template<typename LocationT>
struct PlantZoneState : ZoneState<LocationT>
{
	//saving a mouthful
	using ZoneSlice = zones::Zone_slice;
	using ConstraintSet = std::multimap<std::string, automata::ClockConstraint>;

	PlantZoneState(LocationT location, std::string clock, ZoneSlice zone_slice) :
	ZoneState<LocationT>::ZoneState(location, clock, zone_slice)
	{

	}

	PlantZoneState(LocationT location, std::string clock, ConstraintSet constraints, Endpoint max_constant) :
	ZoneState<LocationT>::ZoneState(location, clock, constraints, max_constant)
	{

	}
};

/** The zone state of an ATA state
 * 
 * An ATAZoneState is a pair (location, set of clock constraints) */
template <typename ConstraintSymbolType>
struct ATAZoneState : ZoneState<logic::MTLFormula<ConstraintSymbolType>>
{
	//saving a mouthful
	using ZoneSlice = zones::Zone_slice;
	using ConstraintSet = std::multimap<std::string, automata::ClockConstraint>;

	ATAZoneState(logic::MTLFormula<ConstraintSymbolType> formula, ZoneSlice zone_slice) :
	ZoneState<logic::MTLFormula<ConstraintSymbolType>>::ZoneState(formula, "", zone_slice)
	{

	}

	ATAZoneState(logic::MTLFormula<ConstraintSymbolType> formula, ConstraintSet constraints, Endpoint max_constant) :
	ZoneState<logic::MTLFormula<ConstraintSymbolType>>::ZoneState(formula, "", constraints, max_constant)
	{

	}
};

/** Print a PlantRegionState. */
template <typename LocationT>
std::ostream &
operator<<(std::ostream &os, const search::PlantRegionState<LocationT> &state)
{
	os << "(" << state.location << ", " << state.clock << ", " << state.symbolic_valuation << ")";
	return os;
}

/** Print an ATARegionState. */
template <typename ConstraintSymbolType>
std::ostream &
operator<<(std::ostream &os, const search::ATARegionState<ConstraintSymbolType> &state)
{
	os << "(" << state.location << ", " << state.symbolic_valuation << ")";
	return os;
}

/** Print a PlantZoneState. */
template <typename LocationT>
std::ostream &
operator<<(std::ostream &os, const search::PlantZoneState<LocationT> &state)
{
	os << "(" << state.location << ", " << state.clock << ", " << state.symbolic_valuation << ")";
	return os;
}

/** Print an ATAZoneState. */
template <typename ConstraintSymbolType>
std::ostream &
operator<<(std::ostream &os, const search::ATAZoneState<ConstraintSymbolType> &state)
{
	os << "(" << state.location << ", " << state.symbolic_valuation << ")";
	return os;
}

} //namespace tacos::search

namespace fmt {

template <typename LocationT>
struct formatter<tacos::search::PlantRegionState<LocationT>> : ostream_formatter
{
};

template <typename ConstraintSymbolType>
struct formatter<tacos::search::ATARegionState<ConstraintSymbolType>> : ostream_formatter
{
};

template <typename LocationT>
struct formatter<tacos::search::PlantZoneState<LocationT>> : ostream_formatter
{
};

template <typename ConstraintSymbolType>
struct formatter<tacos::search::ATAZoneState<ConstraintSymbolType>> : ostream_formatter
{
};
} //namespace fmt