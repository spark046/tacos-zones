#include "automata/ta_zones.h"

#include "automata/automata.h"

namespace tacos::automata {

	//TODO
	/**
	 * @brief Calculates the index for a set of clock constraints for the zone (alternating) timed automaton
	 * 
	 * @param timePoint 
	 * @return RegionIndex 
	 */
	RegionIndex
	AutomatonZones::get_clock_constraints(ClockValuation timePoint) {

	}

	std::set<ClockConstraint>
	get_clock_constraints_from_region_index(RegionIndex         region_index,
	                                        RegionIndex         max_region_index,
	                                        ConstraintBoundType bound_type = ConstraintBoundType::BOTH) {
		//TODO
	}

} // namespace tacos::automata
