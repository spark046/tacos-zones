#pragma once

#include "automata/ata.h"
// TODO Regions should not be TA-specific
#include "automata/ta_regions.h"
#include "mtl/MTLFormula.h"
#include "utilities/numbers.h"
#include "utilities/types.h"

#include <fmt/ostream.h>

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
 * @brief An abstract struct for a symbolic state for either a Plant or an ATA.
 * 
 * A symbolic state always has a location and a symbolic representation of the current valuation.
 * Optionally the name for a specific clock may also exist.
 */
template<typename LocationType, typename SymbolicRepresentationType>
struct SymbolicState
{
	LocationType location;

	std::string clock;

	SymbolicRepresentationType symbolic_valuation;

	SymbolicState() = delete;

	SymbolicState(LocationType location_p, std::string clock_p, SymbolicRepresentationType symbolic_valuation_p) : 
	location(location_p)
	{
		clock = clock_p;
		symbolic_valuation = symbolic_valuation_p;
	}

	/**
	 * @brief calculates what the valuation would become if it was incremented by one step, and then it is returned.
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

/** @brief A regionalized plant state.
 *
 * A PlantRegionState is a tuple (location, clock_name, clock_region) */
template <typename LocationT>
struct PlantRegionState : public SymbolicState<LocationT, RegionIndex>
{
	using Base = SymbolicState<LocationT, RegionIndex>;

	PlantRegionState() = delete;

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

/** @brief A regionalized ATA state.
 *
 * An ATARegionState is a pair (location, clock_region) */
template <typename ConstraintSymbolType>
struct ATARegionState : public SymbolicState<logic::MTLFormula<ConstraintSymbolType>, RegionIndex>
{
	using Base = SymbolicState<logic::MTLFormula<ConstraintSymbolType>, RegionIndex>;

	ATARegionState() = delete;

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

/** @brief The zone state of a plant state.
 *
 * A PlantZoneState is a tuple (location, clock_name, set of clock constraints) */
template <typename LocationT>
struct PlantZoneState
{
	/** The location of the plant zone state */
	LocationT location;
	/** The clock name of this zone state */
	std::string clock;
	/** The index for the set of clock constraints */
	RegionIndex constraints;
};

/** Compare two plant zone states.
 * @param s1 The first state
 * @param s2 The second state
 * @return true if s1 is lexicographically smaller than s2
 */
template <typename LocationT>
bool
operator<(const PlantZoneState<LocationT> &s1, const PlantZoneState<LocationT> &s2)
{
	return std::tie(s1.location, s1.clock, s1.constraints)
	       < std::tie(s2.location, s2.clock, s2.constraints);
}

/** Check two plant zone states for equality.
 * Two plant zone states are considered equal if they have the same location, clock name, and
 * clock constraint index.
 * @param s1 The first state
 * @param s2 The second state
 * @return true if s1 is equal to s2
 */
template <typename LocationT>
bool
operator==(const PlantZoneState<LocationT> &s1, const PlantZoneState<LocationT> &s2)
{
	return !(s1 < s2) && !(s2 < s1);
}

/** @brief The zone state of an ATA state
 * 
 * An ATAZoneState is a pair (location, set of clock constraints) */
template <typename ConstraintSymbolType>
struct ATAZoneState
{
	/** The ATA formula in the zone ATA state */
	logic::MTLFormula<ConstraintSymbolType> formula;
	/** The index of the set of clock constraints */
	RegionIndex constraints;
};

/** Compare two ATA zone states.
 * @param s1 The first state
 * @param s2 The second state
 * @return true if s1 is lexicographically smaller than s2
 */
template <typename ConstraintSymbolType>
bool
operator<(const ATAZoneState<ConstraintSymbolType> &s1, const ATAZoneState<ConstraintSymbolType> &s2)
{
	return std::tie(s1.formula, s1.constraints) < std::tie(s2.formula, s2.constraints);
}

/** Check two ATA zone states for equality.
 * Two ATA zone states are considered equal if they have the same location and clock constraint
 * index.
 * @param s1 The first state
 * @param s2 The second state
 * @return true if s1 is equal to s2
 */
template <typename ConstraintSymbolType>
bool
operator==(const ATAZoneState<ConstraintSymbolType> &s1, const ATAZoneState<ConstraintSymbolType> &s2)
{
	return !(s1 < s2) && !(s2 < s1);
}

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
	os << "(" << state.location << ", " << state.clock << ", " << state.constraints << ")";
	return os;
}

/** Print an ATAZoneState. */
template <typename ConstraintSymbolType>
std::ostream &
operator<<(std::ostream &os, const search::ATAZoneState<ConstraintSymbolType> &state)
{
	os << "(" << state.formula << ", " << state.constraints << ")";
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