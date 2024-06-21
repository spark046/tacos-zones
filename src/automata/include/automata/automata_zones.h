
#include "utilities/types.h"

#include "automata/automata.h"

#include <set>

namespace tacos::automata {
	struct AutomatonZones
	{
		/* Maximum constant which can appear in the clock constraints of the zone */
		unsigned int maximum_constant;

		/* Set of clock constraints, which constitute the zone. I.e. the zone is the set of valuations that satisfy all clock constraints in this set */
		RegionIndex get_clock_constraints(ClockValuation timePoint);
	};

	/** @brief Given a RegionIndex, compute the set of clock constraints that belong to this index.
	 * This index fulfills the following properties:
	 * -The index is even iff the set only contains equality clock constraints (e.g. x = 3) [Ensures that if fractional part is equal to zero, then region index is even]
	 * -The set of clock constraints are normalized by some constant K so that there is only a finite amount of them => If there are n clock constraints, then the maximum index is 2^n
	 * -They are ordered in such a way, so that incrementing them makes some sense, similar to incrementing normal region indices (probably add a function that calculates the "next" zone), in other words time advances. Maybe make incrementation the Delay?
	 * TODO: Figure out other properties that a RegionIndex needs to fulfill
	 * -The order is otherwise given by a set order of clock constraints and then the power set construction for this (i.e. from smallest set to biggest set)
	 * 
	 * @param region_index The region index to construct the constraint for
	 * @param max_region_index The maximal region index that may occur
	 * @param bound_type Whether to construct lower, upper, or both bounds
	 * @return A set (with either one or two elements) of clock constraints that restrict some clock to
	 * the given region
	 */
	std::set<ClockConstraint>
	get_clock_constraints_from_region_index(RegionIndex         region_index,
	                                        RegionIndex         max_region_index,
	                                        ConstraintBoundType bound_type = ConstraintBoundType::BOTH);

}