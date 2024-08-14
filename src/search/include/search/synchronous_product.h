/***************************************************************************
 *  synchronous_product.h - The synchronous product of a TA and an ATA
 *
 *  Created:   Mon 21 Dec 16:13:49 CET 2020
 *  Copyright  2020  Till Hofmann <hofmann@kbsg.rwth-aachen.de>
 *  SPDX-License-Identifier: LGPL-3.0-or-later
 ****************************************************************************/

#pragma once

#include "automata/ata.h"
#include "automata/automata.h"
#include "automata/ta.h"
#include "automata/ta_regions.h"
#include "canonical_word.h"
#include "mtl/MTLFormula.h"
#include "utilities/numbers.h"
#include "utilities/types.h"

#include <spdlog/fmt/ostr.h>
#include <spdlog/spdlog.h>

#include <algorithm>
#include <iterator>
#include <stdexcept>
#include <type_traits>
#include <variant>
#include <float.h>

namespace tacos::search {

/// Increment the region indexes in the configurations of the given ABRegionSymbol.
/** This is a helper function to increase the region index so we reach the next region set.
 * @param configurations The set of configurations to increment the region indexes in
 * @param max_region_index The maximal region index that may never be passed
 * @return A copy of the given configurations with incremented region indexes
 */
template <typename Location, typename ConstraintSymbolType>
std::set<ABRegionSymbol<Location, ConstraintSymbolType>>
increment_region_indexes(
  const std::set<ABRegionSymbol<Location, ConstraintSymbolType>> &configurations,
  RegionIndex                                                     max_region_index)
{
	// Assert that our assumption holds: All region indexes are either odd or even, never mixed, and all configurations are regionalized.
	assert(
	  std::all_of(std::begin(configurations),
				  std::end(configurations),
				  [](const auto &configuration) { return get_region_index(configuration) % 2 == 0; })
	  || std::all_of(std::begin(configurations),
					 std::end(configurations),
					 [](const auto &configuration) {
						 return get_region_index(configuration) % 2 == 1;
					 })
	  || std::all_of(std::begin(configurations),
	  				 std::end(configurations),
					 [](const auto &configuration) { return std::holds_alternative<PlantRegionState<Location>>(configuration) || std::holds_alternative<ATARegionState<ConstraintSymbolType>>(configuration);})
	);
	std::set<ABRegionSymbol<Location, ConstraintSymbolType>> res;
	std::transform(configurations.begin(),
				   configurations.end(),
				   std::inserter(res, res.end()),
				   [max_region_index](auto configuration) {
					   if (std::holds_alternative<PlantRegionState<Location>>(configuration)) {
							auto &ta_configuration = std::get<PlantRegionState<Location>>(configuration);
							
							ta_configuration.increment_valuation(max_region_index);
					   } else {
							auto &ata_configuration =
								std::get<ATARegionState<ConstraintSymbolType>>(configuration);

							ata_configuration.increment_valuation(max_region_index);
					   }
					   return configuration;
				   });
	return res;
}

/**
 * Delays all the states of this configuration to increment all the zones.
 * 
 * @param configurations Set of ABRegionSymbols that are supposed to be zones
 * @param max_region_index Maximal Constant represented as a RegionIndex
 * @return A copy of the set of ABRegionSymbols, but where each zone has been delayed
 */
template <typename Location, typename ConstraintSymbolType>
std::set<ABRegionSymbol<Location, ConstraintSymbolType>>
increment_zones(
  const std::set<ABRegionSymbol<Location, ConstraintSymbolType>> &configurations,
  RegionIndex                                                     max_region_index)
{
	//Make sure this is using zones
	assert(
		std::all_of(std::begin(configurations),
					std::end(configurations),
					[](const auto &configuration) { return  std::holds_alternative<PlantZoneState<Location>>(configuration) ||
															std::holds_alternative<ATAZoneState<ConstraintSymbolType>>(configuration);})
	);

	std::set<ABRegionSymbol<Location, ConstraintSymbolType>> res;
	//Max Constant
	RegionIndex K = (max_region_index - 1) / 2; //Inverse from get_time_successor, not sure why it is done like this

	std::transform( configurations.begin(),
					configurations.end(),
					std::inserter(res, res.end()),
					[K](auto configuration) {
						if (std::holds_alternative<PlantZoneState<Location>>(configuration)) {
							auto &state = std::get<PlantZoneState<Location>>(configuration);

							//TODO: Somehow know the transition to take and only get a subset of these Clock Constraints (Possible? Even Necessary? Hopefully not...)
							//TODO: Get transitions from automata

							state.increment_valuation(K);
						} else { //ATAZoneState
							auto &state = std::get<ATAZoneState<ConstraintSymbolType>>(configuration);

							state.increment_valuation(K);
						}

						return configuration;
					});
	
	return res;
}

/** Get the CanonicalABWord that directly follows the given word. The next word
 * is the word Abs where the Abs_i with the maximal fractional part is
 * incremented such that it goes into the next region. This corresponds to
 * increasing the clock value with the maximal fractional part such that it
 * reaches the next region.
 * @param word The word for which to compute the time successor
 * @param K The upper bound for all constants appearing in clock constraints
 * @return A CanonicalABWord that directly follows the given word time-wise,
 * i.e., all Abs_i in the word Abs are the same except the last component,
 * which is incremented to the next region.
 */
template <typename Location, typename ConstraintSymbolType>
CanonicalABWord<Location, ConstraintSymbolType>
get_time_successor(const CanonicalABWord<Location, ConstraintSymbolType> &word, RegionIndex K)
{
	if (word.empty()) {
		return {};
	}
	CanonicalABWord<Location, ConstraintSymbolType> res;
	const RegionIndex                               max_region_index = 2 * K + 1;
	assert(is_valid_canonical_word(word, max_region_index));

	if(is_region_canonical_word(word)) {
		// Find the partition that contains all maxed partitions. If it does not exist, create an empty
		// one.
		std::set<ABRegionSymbol<Location, ConstraintSymbolType>> new_maxed_partition;
		auto last_nonmaxed_partition = std::next(word.rbegin());
		// Check if maxed partition is actually maxed
		if (std::all_of(word.rbegin()->begin(),
						word.rbegin()->end(),
						[&max_region_index](const auto &configuration) {
							return get_region_index(configuration) == max_region_index;
						})) {
			new_maxed_partition = *word.rbegin();
		} else {
			// There is no maxed partition, so the last partition is already nonmaxed.
			last_nonmaxed_partition = word.rbegin();
		}
		if (last_nonmaxed_partition == word.rend()) {
			// All partitions are maxed, nothing to increment.
			return word;
		}

		const bool has_even_region_index = get_region_index(*word.begin()->begin()) % 2 == 0;
		// The first set needs to be incremented if its region indexes are even.
		if (has_even_region_index) {
			auto incremented = increment_region_indexes(*word.begin(), max_region_index);
			std::set<ABRegionSymbol<Location, ConstraintSymbolType>> incremented_nonmaxed;
			for (auto &configuration : incremented) {
				if (get_region_index(configuration) == max_region_index) {
					new_maxed_partition.insert(configuration);
				} else {
					incremented_nonmaxed.insert(configuration);
				}
			}
			if (!incremented_nonmaxed.empty()) {
				res.push_back(std::move(incremented_nonmaxed));
			}
			std::reverse_copy(last_nonmaxed_partition, std::prev(word.rend()), std::back_inserter(res));
		} else {
			// Increment the last nonmaxed partition. If we have a new maxed configuration, put it into the
			// maxed partition. Otherwise, keep it in place.
			auto incremented = increment_region_indexes(*last_nonmaxed_partition, max_region_index);
			std::set<ABRegionSymbol<Location, ConstraintSymbolType>> incremented_nonmaxed;
			for (auto &configuration : incremented) {
				if (get_region_index(configuration) == max_region_index) {
					new_maxed_partition.insert(configuration);
				} else {
					incremented_nonmaxed.insert(configuration);
				}
			}
			if (!incremented_nonmaxed.empty()) {
				res.push_back(std::move(incremented_nonmaxed));
			}
			std::reverse_copy(std::next(last_nonmaxed_partition), word.rend(), std::back_inserter(res));
		}

		// If the maxed partition is non-empty, add it to the resulting word.
		if (!new_maxed_partition.empty()) {
			res.push_back(std::move(new_maxed_partition));
		}
	} else { //Using zones
		for(const auto &partition : word) {
			res.push_back(increment_zones(partition, max_region_index));
		}
	}

	assert(is_valid_canonical_word(res, max_region_index));
	return res;
}

/**
 * @brief Get a concrete candidate-state for a given valid canonical word. The
 * candidate consists of a concrete TA-state and a concrete ATA-state.
 * @tparam Location The location type for timed automata locations
 * @tparam ConstraintSymbolType The type of actions which encode locations in the ATA
 * @param word The passed canonical word for which a candidate should be generated
 * @param clock_constraints A set of clock constraints that should be fulfilled by the candidate. Necessary for zones
 * @return std::pair<TAConfiguration<Location>, ATAConfiguration<ConstraintSymbolType>> A pair of
 * TA- and ATA-state which can be represented by the passed canonical word
 */
template <typename Location /* TA::Location */, typename ConstraintSymbolType>
std::pair<PlantConfiguration<Location>, ATAConfiguration<ConstraintSymbolType>>
get_candidate(const CanonicalABWord<Location, ConstraintSymbolType> &word)
{
	assert(is_valid_canonical_word(word));
	PlantConfiguration<Location>           plant_configuration{};
	ATAConfiguration<ConstraintSymbolType> ata_configuration{};
	const Time                             time_delta = Time(1) / Time(word.size() + 1);
	for (std::size_t i = 0; i < word.size(); i++) {
		const auto &abs_i = word[i];
		for (const ABRegionSymbol<Location, ConstraintSymbolType> &symbol : abs_i) {
			// TODO Refactor, fractional/integral outside of if
			if (std::holds_alternative<PlantRegionState<Location>>(symbol)) {
				const auto       &ta_region_state = std::get<PlantRegionState<Location>>(symbol);
				const RegionIndex region_index    = ta_region_state.symbolic_valuation;
				const Time        fractional_part =
					region_index % 2 == 0 ? 0 : time_delta * static_cast<Time>((i + 1));
				const Time  integral_part = static_cast<RegionIndex>(region_index / 2);
				const auto &clock_name    = ta_region_state.clock;
				// update ta_configuration
				plant_configuration.location                     = ta_region_state.location;
				plant_configuration.clock_valuations[clock_name] = integral_part + fractional_part;
			} else if(std::holds_alternative<ATARegionState<ConstraintSymbolType>>(symbol)) { // ATARegionState<ConstraintSymbolType>
				const auto       &ata_region_state = std::get<ATARegionState<ConstraintSymbolType>>(symbol);
				const RegionIndex region_index     = ata_region_state.symbolic_valuation;
				const Time        fractional_part =
					region_index % 2 == 0 ? 0 : time_delta * static_cast<Time>((i + 1));
				const Time integral_part = static_cast<RegionIndex>(region_index / 2);
				// update configuration
				// TODO check: the formula (aka ConstraintSymbolType) encodes the location, the clock
				// valuation is separate and a configuration is a set of such pairs. Is this already
				// sufficient?
				ata_configuration.insert(ATAState<ConstraintSymbolType>{ata_region_state.location,
																		fractional_part + integral_part});
			} else if(std::holds_alternative<PlantZoneState<Location>>(symbol)) {
				const auto &ta_zone_state = std::get<PlantZoneState<Location>>(symbol);

				plant_configuration.location = ta_zone_state.location;

				const auto &clock_name = ta_zone_state.clock;
				zones::Zone_slice zone = ta_zone_state.symbolic_valuation;

				if(zone.lower_isOpen_) //Check if we can have an integer or not
				{
					plant_configuration.clock_valuations[clock_name] = ((ClockValuation) zone.lower_bound_) + time_delta;
				} else {
					plant_configuration.clock_valuations[clock_name] = (ClockValuation) zone.lower_bound_;
				}
			} else { //ATAZoneState
				const auto &ata_zone_state = std::get<ATAZoneState<ConstraintSymbolType>>(symbol);
				zones::Zone_slice zone = ata_zone_state.symbolic_valuation;

				if(zone.lower_isOpen_) //Check if we can have an integer or not
				{
					ata_configuration.insert(ATAState<ConstraintSymbolType>{ata_zone_state.location, ((ClockValuation) zone.lower_bound_) + time_delta});
				} else {
					ata_configuration.insert(ATAState<ConstraintSymbolType>{ata_zone_state.location, (ClockValuation) zone.lower_bound_});
				}
			}
		}
	}
	return std::make_pair(plant_configuration, ata_configuration);
}

/** Get the nth time successor. */
template <typename Location, typename ConstraintSymbolType>
CanonicalABWord<Location, ConstraintSymbolType>
get_nth_time_successor(const CanonicalABWord<Location, ConstraintSymbolType> &word,
					   RegionIndex                                            n,
					   RegionIndex                                            K)
{
	auto res = word;
	for (RegionIndex i = 0; i < n; i++) {
		res = get_time_successor(res, K);
	}
	return res;
}

/** Compute all time successors of a canonical word.
 * @param canonical_word The canonical word to compute the time successors of
 * @param K The maximal constant
 * @return All time successors of the word along with the region increment to reach the successor
 */
template <typename Location, typename ConstraintSymbolType>
std::vector<std::pair<RegionIndex, CanonicalABWord<Location, ConstraintSymbolType>>>
get_time_successors(const CanonicalABWord<Location, ConstraintSymbolType> &canonical_word,
					
					RegionIndex                                            K)
{
	//TODO: Compute cur_index differently for zones to allow for taking more than one time step at once
	SPDLOG_TRACE("Computing time successors of {} with K={}", canonical_word, K);
	auto        cur = get_time_successor(canonical_word, K);
	RegionIndex cur_index{0};
	std::vector<std::pair<RegionIndex, CanonicalABWord<Location, ConstraintSymbolType>>>
	  time_successors;
	time_successors.push_back(std::make_pair(cur_index++, canonical_word));
	for (; cur != time_successors.back().second; cur_index++) {
		time_successors.emplace_back(cur_index, cur);
		cur = get_time_successor(time_successors.back().second, K);
	}
	return time_successors;
}
/** Compute the direct time successors which introduce an increment in the ATA configuration for each of the passed words.
 * @param canonical_words The set of canonical words to compute time successors of
 * @param K The maximal constant
 * @return All direct time successors of the passed words
 */
template <typename Location, typename ConstraintSymbolType>
std::set<CanonicalABWord<Location, ConstraintSymbolType>>
get_next_time_successors(
  const std::set<CanonicalABWord<Location, ConstraintSymbolType>> &canonical_words,
  RegionIndex                                                      K)
{
	assert(!canonical_words.empty());
	assert(std::all_of(std::begin(canonical_words), std::end(canonical_words), [&](const auto &word) {
		return reg_a(word) == reg_a(*std::begin(canonical_words));
	}));
	std::set<CanonicalABWord<Location, ConstraintSymbolType>> successors;
	std::map<CanonicalABWord<Location, ConstraintSymbolType>,
			 CanonicalABWord<Location, ConstraintSymbolType>>
	  successors_map;
	for (const auto &word : canonical_words) {
		successors_map[word] = get_time_successor(word, K);
	}
	if (std::any_of(std::begin(successors_map), std::end(successors_map), [](const auto &map_entry) {
			return reg_a(map_entry.first) == reg_a(map_entry.second);
		})) {
		// There is at least one where the successor has the same reg_a and thus there is an ATA
		// configuration that is incremented. We must only increments those where there is also an ATA
		// configuration to increment.
		for (const auto &[word, successor] : successors_map) {
			if (reg_a(word) == reg_a(successor)) {
				successors.insert(successor);
			} else {
				successors.insert(word);
			}
		}
	} else {
		for (const auto &[_, successor] : successors_map) {
			successors.insert(successor);
		}
	}
	return successors;
}

/** Compute all time successors of a set of canonical words (i.e., of a node in the search tree).
 * @param canonical_words A set of canonical words to compute the time successors of
 * @param K The maximal constant
 * @return A map of time successors of each word along with the region increment to reach the
 * successor
 */
template <typename Location, typename ConstraintSymbolType>
std::vector<std::set<CanonicalABWord<Location, ConstraintSymbolType>>>
get_time_successors(
  const std::set<CanonicalABWord<Location, ConstraintSymbolType>> &canonical_words,
  RegionIndex                                                      K)
{
	std::vector<std::set<CanonicalABWord<Location, ConstraintSymbolType>>> successors;
	successors.push_back(canonical_words);

	if(is_region_canonical_word(*canonical_words.begin())) {
		successors.push_back(get_next_time_successors(canonical_words, K));
		return successors;
	}

	while (true) {
		const auto next = get_next_time_successors(successors.back(), K);
		if (next != successors.back()) {
			successors.push_back(next);
		} else {
			break;
		}
	}
	return successors;
}

} // namespace tacos::search