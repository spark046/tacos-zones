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
public:
	LocationType location;

	std::string clock;

	SymbolicRepresentationType symbolic_valuation;

	SymbolicState(LocationType location_p, std::string clock_p, SymbolicRepresentationType symbolic_valuation_p) : 
	location(location_p)
	{
		clock = clock_p;
		symbolic_valuation = symbolic_valuation_p;
	}

	/**
	 * Calculates what the valuation would become if it was incremented by one step, and then it is returned.
	 * 
	 * The state itself does not directly change from this.
	 * 
	 * @return The incremented valuation
	 */
	virtual SymbolicRepresentationType get_increment_valuation() const = 0;

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


	RegionIndex get_increment_valuation() const
	{
		return Base::symbolic_valuation + 1;
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

	RegionIndex get_increment_valuation() const
	{
		return Base::symbolic_valuation + 1;
	}
};

/** A zone state that can be for either a Plant or an ATA.
 *
 * A ZoneState is a tuple (location, clock_name, set of clock constraints)
 * (This is effectively a PlantZoneState, but is kept seperate to preserve proper inheritance relations with ATAZoneState)
 */
template <typename LocationType>
struct ZoneState : public SymbolicState<LocationType, std::map<std::string, zones::Zone_slice>>
{
	//saving a mouthful
	using ZoneSlices = std::map<std::string, zones::Zone_slice>;
	//saving a second mouthful
	using Base = SymbolicState<LocationType, ZoneSlices>;

	ZoneState(LocationType location_p, std::string clock_p, ZoneSlices constraints_p) : 
	Base::SymbolicState(location_p, clock_p, constraints_p)
	{

	}

	/** Overloaded Constructor allowing the use of a set of ClockConstraints to initialize a ZoneState */
	ZoneState(LocationType location_p, std::string clock_p, std::multimap<std::string, automata::ClockConstraint> clock_constraint) :
	Base::SymbolicState(location_p, clock_p, [&clock_constraint](){
		ZoneSlices ret = {};
		for(auto iter1 = clock_constraint.begin(); iter1 != clock_constraint.end(); iter1++)
		{
			ret.insert( {iter1->first, zones::Zone_slice{iter1->second} } );
		}
		return ret;
	}())
	{

	}

	/**
	 * Returns an incremented zone by delaying it.
	 * 
	 * A zone is delayed by incrementing all clock valuations by any arbitrary amount.
	 * 
	 * In particular, this means all equality constraints become greater equal constraints, all less (and equal)
	 * constraints disappear, and all greater (and equal) constraints remain.
	 * Not equal constraints also disappear, as long as it is not the smallest constant, i.e. there could have been
	 * a valuation below it to delay into the inequality.
	 * 
	 * @return A multimap consisting of all the new constraints (and missing the unnecessary ones).
	 */
	ZoneSlices get_increment_valuation() const
	{
		Endpoint max_valuation = std::numeric_limits<Endpoint>::max(); //TODO: Make this a parameter
		ZoneSlices currentZone = Base::symbolic_valuation;
		ZoneSlices delayZone = {};

		for(auto iter1 = currentZone.begin(); iter1 != currentZone.end(); iter1++)
		{
			if(iter1->second.upper_bound_ >= max_valuation)
			{
				delayZone.insert( {iter1->first, iter1->second} );
			} else {
				zones::Zone_slice newSlice = zones::Zone_slice(iter1->second.lower_bound_, max_valuation, iter1->second.lower_isStrict_, false);
				delayZone.insert( {iter1->first, newSlice} );
			}
		}

		return delayZone;
	}

	/** Compare two zone states.
	 * 
	 * TODO: Symbolic Time comparison probably does not work yet due to multimap
	 * 
	 * @param s1 The first state
	 * @param s2 The second state
	 * @return true if s1 is lexicographically smaller than s2
	 */
	friend bool
	operator<(const ZoneState<LocationType> &s1, const ZoneState<LocationType> &s2)
	{
		return std::tie(s1.location, s1.clock)
		       < std::tie(s2.location, s2.clock);
	}
	
	/** Check two zone states for equality.
	 * Two symbolic states are considered equal if they have the same location(, clock name), and
	 * symbolic time.
	 * 
	 * TODO: Symbolic Time probably does not work yet due to multimap
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
	using ZoneSlices = std::map<std::string, zones::Zone_slice>;
	using ConstraintSet = std::multimap<std::string, automata::ClockConstraint>;

	PlantZoneState(LocationT location, std::string clock, ZoneSlices zone) :
	ZoneState<LocationT>::ZoneState(location, clock, zone)
	{

	}

	PlantZoneState(LocationT location, std::string clock, ConstraintSet constraints) :
	ZoneState<LocationT>::ZoneState(location, clock, constraints)
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
	using ZoneSlices = std::map<std::string, zones::Zone_slice>;
	using ConstraintSet = std::multimap<std::string, automata::ClockConstraint>;

	ATAZoneState(ConstraintSymbolType location, std::string clock, ZoneSlices zone) :
	ZoneState<ConstraintSymbolType>::ZoneState(location, clock, zone)
	{

	}

	ATAZoneState(logic::MTLFormula<ConstraintSymbolType> formula, ConstraintSet constraints) :
	ZoneState<logic::MTLFormula<ConstraintSymbolType>>::ZoneState(formula, "", constraints)
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