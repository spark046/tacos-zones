/***************************************************************************
 *  reg_a.h - Definition of the function reg_a(w)
 *
 *  Created:   Fri  5 Feb 14:25:02 CET 2021
 *  Copyright  2021  Till Hofmann <hofmann@kbsg.rwth-aachen.de>
 *  SPDX-License-Identifier: LGPL-3.0-or-later
 ****************************************************************************/


#pragma once

#include "canonical_word.h"

#include <variant>

namespace tacos::search {

/** Compute reg_a(w), which is w with all configuration components from B omitted.
 * The resulting word only contains configurations from the timed automaton A.
 * This is for regions.
 * @param word The region word to compute reg_a(word) of
 * @return The word reg_a(word), which is the same as word, but without any configurations from the
 * ATA
 */
template <typename Location, typename ConstraintSymbolType>
CanonicalABWord<Location, ConstraintSymbolType>
reg_a(const CanonicalABWord<Location, ConstraintSymbolType> &word)
{
	CanonicalABWord<Location, ConstraintSymbolType> res;
	for (const auto &partition : word) {
		std::set<ABRegionSymbol<Location, ConstraintSymbolType>> res_i;
		for (const auto &ab_symbol : partition) {
			if (std::holds_alternative<PlantRegionState<Location>>(ab_symbol)) {
				res_i.insert(ab_symbol);
			} else if(std::holds_alternative<PlantZoneState<Location>>(ab_symbol)) {
				res_i.insert(ab_symbol);
			}
		}
		// TODO check if we can just skip the whole partition
		if (!res_i.empty()) {
			res.push_back(res_i);
		}
	}
	return res;
}

/** Compute reg_a(w), which is w with all configuration components from B omitted.
 * The resulting word only contains configurations from the timed automaton A.
 * This is for zone.
 * @param word The zone word to compute reg_a(word) of
 * @return The word reg_a(word), which is the same as word, but without any configurations from the
 * ATA
 */
template <typename Location, typename ConstraintSymbolType>
CanonicalABZoneWord<Location, ConstraintSymbolType>
reg_a(const CanonicalABZoneWord<Location, ConstraintSymbolType> &word)
{
	auto new_dbm = word.dbm.get_subset(word.ta_clocks);

	return CanonicalABZoneWord<Location, ConstraintSymbolType>{word.ta_location, word.ta_clocks, {}, new_dbm};
}

} // namespace tacos::search
