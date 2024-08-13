/***************************************************************************
 *  canonical_word.h - Canonical word representation
 *
 *  Created:   Fri  5 Mar 16:38:43 CET 2021
 *  Copyright  2021  Till Hofmann <hofmann@kbsg.rwth-aachen.de>
 *  SPDX-License-Identifier: LGPL-3.0-or-later
 ****************************************************************************/

#pragma once

#include "automata/ata.h"

#include <fmt/ostream.h>
#include "symbolic_state.h"
// TODO Regions should not be TA-specific
#include "automata/ta_regions.h"
#include "mtl/MTLFormula.h"
#include "utilities/numbers.h"
#include "utilities/types.h"

/** Get the regionalized synchronous product of a TA and an ATA. */
namespace tacos::search {

/** An ABSymbol is either a PlantState or an ATAState */
template <typename LocationT, typename ConstraintSymbolType>
using ABSymbol = std::variant<PlantState<LocationT>, ATAState<ConstraintSymbolType>>;

/** An ABRegionSymbol is either a TARegionState or an ATARegionState */
template <typename LocationT, typename ConstraintSymbolType>
using ABRegionSymbol =
  std::variant<PlantRegionState<LocationT>, ATARegionState<ConstraintSymbolType>,
			   PlantZoneState<LocationT>, ATAZoneState<ConstraintSymbolType> >;

/** A canonical word H(s) for a regionalized A/B configuration */
template <typename LocationT, typename ConstraintSymbolT>
using CanonicalABWord = std::vector<std::set<ABRegionSymbol<LocationT, ConstraintSymbolT>>>;

/** Get the clock valuation for an ABSymbol, which is either a TA state or an ATA state.
 * @param w The symbol to read the time from
 * @return The clock valuation in the given state
 */
template <typename Location, typename ConstraintSymbolType>
ClockValuation
get_time(const ABSymbol<Location, ConstraintSymbolType> &w)
{
	if (std::holds_alternative<PlantState<Location>>(w)) {
		return std::get<PlantState<Location>>(w).clock_valuation;
	} else {
		return std::get<ATAState<ConstraintSymbolType>>(w).clock_valuation;
	}
}

/** Get the region index for a regionalized ABRegionSymbol, which is either a
 * TARegionState or an ATARegionState. It can also be a ZoneState, in which case the smallest region_index of the zone is returned.
 * 
 * The smallest RegionIndex is returned for zones, since get_region_index is also used for checking whether a configuration is maximized.
 * TODO: Let this function only be used for Regions
 * @param w The symbol to read the time from
 * @return The region index in the given state. For zones, this is smallest region index that is in the zone.
 */
template <typename Location, typename ConstraintSymbolType>
RegionIndex
get_region_index(const ABRegionSymbol<Location, ConstraintSymbolType> &w)
{
	if (std::holds_alternative<PlantRegionState<Location>>(w)) {
		return std::get<PlantRegionState<Location>>(w).symbolic_valuation;
	} else if(std::holds_alternative<ATARegionState<ConstraintSymbolType>>(w)) {
		return std::get<ATARegionState<ConstraintSymbolType>>(w).symbolic_valuation;
	} else if(std::holds_alternative<PlantZoneState<Location>>(w)) {
		zones::Zone_slice zone = std::get<PlantZoneState<Location>>(w).symbolic_valuation;

		return 2 * zone.upper_bound_ + 1; //same definition as in search::get_time_successor
	} else { //ATAZoneState
		zones::Zone_slice zone = std::get<ATAZoneState<ConstraintSymbolType>>(w).symbolic_valuation;

		return 2 * zone.upper_bound_ + 1; //same definition as in search::get_time_successor
	}
}

/** Get the Zone for an ABRegionSymbol using zones.
 * This ABRegionSymbol should be either a PlantZoneState or an ATAZoneState.
 * If it is one of the regionalized states, the interval that represents the region is returned as a fallback.
 * 
 * @param w The ABRegionSymbol
 * @return The zone slice of the symbol. If the symbol was regionalized, the region is converted to an interval and returned
 */
template <typename Location, typename ConstraintSymbolType>
zones::Zone_slice
get_zone_slice(const ABRegionSymbol<Location, ConstraintSymbolType> &w, RegionIndex max_region_index)
{
	if (std::holds_alternative<PlantRegionState<Location>>(w)) {
		RegionIndex i = std::get<PlantRegionState<Location>>(w).symbolic_valuation;

		if(i % 2 == 0) {
			return zones::Zone_slice{i/2, i/2, false, false, max_region_index};
		} else {
			return zones::Zone_slice{i/2, i/2 + 1, true, true, max_region_index};
		}
	} else if(std::holds_alternative<ATARegionState<ConstraintSymbolType>>(w)) {
		RegionIndex i = std::get<ATARegionState<ConstraintSymbolType>>(w).symbolic_valuation;

		if(i % 2 == 0) {
			return zones::Zone_slice{i/2, i/2, false, false, max_region_index};
		} else {
			return zones::Zone_slice{i/2, i/2 + 1, true, true, max_region_index};
		}
	} else if(std::holds_alternative<PlantZoneState<Location>>(w)) {
		return std::get<PlantZoneState<Location>>(w).symbolic_valuation;
	} else { //ATAZoneState
		return std::get<ATAZoneState<ConstraintSymbolType>>(w).symbolic_valuation;
	}
}

/** @brief Thrown if a canonical word is not valid. */
class InvalidCanonicalWordException : public std::domain_error
{
public:
	/** Construct the exception with a single message
	 * @param message The exact error that occurred
	 */
	explicit InvalidCanonicalWordException(const std::string &message)
	: std::domain_error(""), message_(message)
	{
	}

	/** Construct the exception with the word and a message
	 * @param word The word that is invalid
	 * @param error The error that occurred
	 */
	template <typename Location, typename ConstraintSymbolType>
	explicit InvalidCanonicalWordException(
	  const CanonicalABWord<Location, ConstraintSymbolType> &word,
	  const std::string                                     &error)
	: std::domain_error("")
	{
		std::stringstream msg;
		msg << "Invalid word: '" << word << "': " << error;
		message_ = msg.str();
	}

	/** Get the exact error message
	 * @return A message describing the error in detail
	 */
	const char *
	what() const noexcept override
	{
		return message_.c_str();
	}

private:
	std::string message_;
};

/** Validate a canonical word.
 * Check a word whether it is a valid canonical word. Throws an exception if this is not the case.
 * @param word The word to check
 * @param max_region The maximal region index that may occur in the canonical word
 * @return true if the word is a valid canonical word
 */
template <typename Location, typename ConstraintSymbolType>
bool
is_valid_canonical_word(const CanonicalABWord<Location, ConstraintSymbolType> &word,
                        RegionIndex                                            max_region = 0)
{
	// TODO all ta_symbols should agree on the same location
	// TODO clocks must have unique values (i.e., must not occur multiple times)
	if (word.empty()) {
		throw InvalidCanonicalWordException(word, "word is empty");
	}
	// No configuration should be empty
	if (std::any_of(word.begin(), word.end(), [](const auto &configurations) {
		    return configurations.empty();
	    })) {
		throw InvalidCanonicalWordException(word, "word contains an empty configuration");
	}

	// There cannot be both regionalized ABSymbols and ABSymbols using zones.
	//Check whether the "first" element is regionalized or not, we then check whether the rest matches
	bool regionalized = (std::holds_alternative<PlantRegionState<Location>>(*word[0].begin()) ||
						 std::holds_alternative<ATARegionState<ConstraintSymbolType>>(*word[0].begin()) );

	std::for_each(word.begin(), word.end(), [&word, regionalized](const auto &configurations) {
		if(regionalized) {
			if (std::any_of(configurations.begin(),
							configurations.end(),
							[](const auto &w) { return (std::holds_alternative<PlantZoneState<Location>>(w) ||
														std::holds_alternative<ATAZoneState<ConstraintSymbolType>>(w)); }))
			{
				throw InvalidCanonicalWordException(word, "Word contains both regionalized and zone configurations");
			}
		} else {
			if (std::any_of(configurations.begin(),
							configurations.end(),
							[](const auto &w) { return (std::holds_alternative<PlantRegionState<Location>>(w) ||
														std::holds_alternative<ATARegionState<ConstraintSymbolType>>(w)); }))
			{
				throw InvalidCanonicalWordException(word, "Word contains both regionalized and zone configurations");
			}
		}

	});

	if(regionalized)
	{
		// There must be no configuration with a region larger than the max region index.
		if (max_region > 0) {
			if (std::any_of(word.begin(), word.end(), [max_region](const auto &configurations) {
				    return std::any_of(configurations.begin(),
				                       configurations.end(),
				                       [max_region](const auto &w) {
					                       return get_region_index(w) > max_region;
				                       });
			    })) {
				throw InvalidCanonicalWordException(
				  word, "word contains configuration with a region larger than the max region");
			};
		}

		// Each partition either contains only even or only odd region indexes. This is because the word
		// is partitioned by the fractional part and the region index can only be even if the fractional
		// part is 0. If that is the case, there cannot be any configuration with an odd region index in
		// the same partition, as that configuration's fractional part would be > 0.
		std::for_each(word.begin(), word.end(), [&word](const auto &configurations) {
			if (std::any_of(configurations.begin(),
			                configurations.end(),
			                [](const auto &w) { return get_region_index(w) % 2 == 0; })
			    && std::any_of(configurations.begin(), configurations.end(), [](const auto &w) {
				       return get_region_index(w) % 2 == 1;
			       })) {
				throw InvalidCanonicalWordException(word, "both odd and even region indexes");
			}
		});

		// There must be at most one partition with fractional part 0.
		// The only partition that is allowed to have fracitonal part 0 is the 0th
		// partition.
		std::for_each(std::next(word.begin()), word.end(), [&word](const auto &configurations) {
			std::for_each(configurations.begin(), configurations.end(), [&word](const auto &w) {
				if (get_region_index(w) % 2 == 0) {
					throw InvalidCanonicalWordException(word,
					                                    "fractional part 0 in wrong element of partition");
				}
			});
		});
	} else {
		//There must be no invalid zone or zone exceeding the max region index.
		//Max Constant
		RegionIndex K;
		if(max_region % 2 == 0) {
			K = max_region / 2;
		} else {
			K = (max_region + 1) / 2;
		}

		std::for_each(word.begin(), word.end(), [&word, max_region](const auto &configurations) {
			if (std::any_of(configurations.begin(),
			                configurations.end(),
			                [max_region](const auto &w) { return !zones::is_valid_zone(get_zone_slice(w, max_region)); })
				) {
				throw InvalidCanonicalWordException(word, "word contains configuration with an invalid zone");
			}
		});

		std::for_each(word.begin(), word.end(), [&word, K, max_region](const auto &configurations) {
			if (std::any_of(configurations.begin(),
			                configurations.end(),
			                [K, max_region](const auto &w) { return(get_zone_slice(w, max_region).lower_bound_ > K ||
																	get_zone_slice(w, max_region).upper_bound_ > K ||
																	get_zone_slice(w, max_region).max_constant_ > K) &&
																	K != 0; })
				) {
				throw InvalidCanonicalWordException(word, "word contains configuration with a zone that has bounds exceeding the max region");
			}
		});
	}

	return true;
}

/**
 * @brief Checks whether a canonical word is using regions or not.
 * 
 * @param word The canonical word being checked
 * @return True if canonical word uses region, false if it uses zones
 */
template <typename Location, typename ConstraintSymbolType>
bool
is_region_canonical_word(const CanonicalABWord<Location, ConstraintSymbolType> &word)
{
	assert(is_valid_canonical_word(word));

	return (std::holds_alternative<PlantRegionState<Location>>(*word[0].begin()) || std::holds_alternative<ATARegionState<ConstraintSymbolType>>(*word[0].begin()) );
}

/**
 * Gets the location of the TA State within the canonical ABWord.
 * The CanonicalABWord must/should have only one TA-Configuration, i.e. potentially multiple clocks at the same location
 * 
 * @param word CanonicalABWord
 * 
 * @return The location of the TA-Configuration
 */
template <typename Location, typename ConstraintSymbolType>
Location
get_canonical_word_ta_location(const CanonicalABWord<Location, ConstraintSymbolType> &word)
{
	//Since a CanonicalABWord only has one TA-Configuration, we just have to check the first PlantRegionState/PlantZoneState
	for(const auto &partition : word) {
		for(const auto &symbol : partition) {
			if(std::holds_alternative<PlantZoneState<Location>>(symbol)) {
				auto state = std::get<PlantZoneState<Location>>(symbol);

				return state.location;
			} else if(std::holds_alternative<PlantRegionState<Location>>(symbol)) {
				auto state = std::get<PlantRegionState<Location>>(symbol);

				return state.location;
			}
		}
	}

	//Somehow there was no TA-Configuration, which should be impossible
	assert(false);

	//Necessary Rubbish
	Location l = Location();
	return l;
}

/**
 * Get a map of the zone_slice for each clock within a CanonicalABWord
 * 
 * @param word A CanonicalABWord which uses zones
 * 
 * @return A map where the key is the clock name and the value is the Zone_slice (clock, Zone)
 */
template <typename Location, typename ConstraintSymbolType>
std::map<std::string, zones::Zone_slice>
get_canonical_word_zones(const CanonicalABWord<Location, ConstraintSymbolType> &word)
{
	//NOT a regionalized canonical word
	assert(!is_region_canonical_word(word));

	std::map<std::string, zones::Zone_slice> ret;

	for(const auto &partition : word) {
		for(const auto &symbol : partition) {
			if(std::holds_alternative<PlantZoneState<Location>>(symbol)) {
				const auto &state = std::get<PlantZoneState<Location>>(symbol);

				ret.insert( {state.clock, state.symbolic_valuation} );
			} else { //ATAZoneState
				const auto &state = std::get<ATAZoneState<ConstraintSymbolType>>(symbol);

				ret.insert( {"", state.symbolic_valuation} );
			}
		}
	}

	return ret;
}

/**
 * Gets a set of ABRegionSymbols that are ATAZoneStates
 * 
 * @param word A canonical word using zones
 * @return A std::set of ATAZoneStates
 */
template <typename Location, typename ConstraintSymbolType>
std::set<ATAZoneState<ConstraintSymbolType>>
get_ata_symbols_from_canonical_word(const CanonicalABWord<Location, ConstraintSymbolType> &word)
{
	std::set<ATAZoneState<ConstraintSymbolType>> ret;

	for(const auto &partition : word) {
		for(const auto &symbol : partition) {
			if(std::holds_alternative<ATAZoneState<ConstraintSymbolType>>(symbol)) {
				auto state = std::get<ATAZoneState<ConstraintSymbolType>>(symbol);

				ret.insert( state );
			}
		}
	}

	return ret;
}

/** Get the canonical word H(s) for the given A/B configuration s, closely
 * following Bouyer et al., 2006. The TAStates of s are first expanded into
 * triples (location, clock, valuation) (one for each clock), and then merged
 * with the pairs from the ATAConfiguration. The resulting set is then
 * partitioned according to the fractional part of the clock valuations. Then,
 * each tuple is regionalized by replacing the clock valuation with the
 * respective region index.  The resulting word is a sequence of sets, each set
 * containing regionalized tuples that describe a TAState or ATAState. The
 * sequence is sorted by the fractional part of the original clock valuations.
 * @param plant_configuration The configuration of the plant A (e.g., a TA
 * configuration)
 * @param ata_configuration The configuration of the alternating timed automaton B
 * @param K The value of the largest constant any clock may be compared to
 * @param zones Whether the canonical word is for a zone construction
 * @param clock_constraints The set of all clock constraints present in either the plant or the ata
 * @return The canonical word representing the state s, as a sorted vector of
 * sets of tuples (triples from A and pairs from B).
 */
template <typename Location, typename ConstraintSymbolType>
CanonicalABWord<Location, ConstraintSymbolType>
get_canonical_word(const PlantConfiguration<Location>           &plant_configuration,
                   const ATAConfiguration<ConstraintSymbolType> &ata_configuration,
                   const unsigned int                            K,
				   const bool zones = false,
				   const std::multimap<std::string, automata::ClockConstraint> clock_constraints = {}
				   )
{
	using ABSymbol       = ABSymbol<Location, ConstraintSymbolType>;
	using ABRegionSymbol = ABRegionSymbol<Location, ConstraintSymbolType>;
	// TODO Also accept a TA that does not have any clocks.
	if (plant_configuration.clock_valuations.empty()) {
		throw std::invalid_argument("TA without clocks are not supported");
	}
	std::set<ABSymbol> g;
	// Insert ATA configurations into g.
	std::copy(ata_configuration.begin(), ata_configuration.end(), std::inserter(g, g.end()));
	// Insert TA configurations into g.
	for (const auto &[clock_name, clock_value] : plant_configuration.clock_valuations) {
		g.insert(PlantState<Location>{plant_configuration.location, clock_name, clock_value});
	}
	// Sort into partitions by the fractional parts.
	std::map<ClockValuation, std::set<ABSymbol>, utilities::ApproxFloatComparator<Time>>
	  partitioned_g(utilities::ApproxFloatComparator<Time>{});
	for (const ABSymbol &symbol : g) {
		partitioned_g[utilities::getFractionalPart<int, ClockValuation>(get_time(symbol))].insert(
		  symbol);
	}

	if(!zones) {
		// Replace exact clock values by region indices.
		automata::ta::TimedAutomatonRegions             regionSet{K};
		CanonicalABWord<Location, ConstraintSymbolType> abs;
		for (const auto &[fractional_part, g_i] : partitioned_g) {
			std::set<ABRegionSymbol> abs_i;
			std::transform(
			  g_i.begin(),
			  g_i.end(),
			  std::inserter(abs_i, abs_i.end()),
			  [&](const ABSymbol &w) -> ABRegionSymbol {
				  if (std::holds_alternative<PlantState<Location>>(w)) {
					  const PlantState<Location> &s = std::get<PlantState<Location>>(w);
					  return PlantRegionState<Location>(s.location,
					                                    s.clock,
					                                    regionSet.getRegionIndex(s.clock_valuation));
				  } else {
					  const ATAState<ConstraintSymbolType> &s = std::get<ATAState<ConstraintSymbolType>>(w);
					  return ATARegionState<ConstraintSymbolType>(s.location,
					                                              regionSet.getRegionIndex(s.clock_valuation));
				  }
			  });
			abs.push_back(abs_i);
		}
		assert(is_valid_canonical_word(abs, 2 * K + 1));
		return abs;
	} else { //zones
		CanonicalABWord<Location, ConstraintSymbolType> abs;

		for (const auto &[fractional_part, g_i] : partitioned_g) {
			std::set<ABRegionSymbol> abs_i;
			std::transform(
				g_i.begin(),
				g_i.end(),
				std::inserter(abs_i, abs_i.end()),
				[&](const ABSymbol &w) -> ABRegionSymbol {
					if (std::holds_alternative<PlantState<Location>>(w)) {
						const PlantState<Location> &s = std::get<PlantState<Location>>(w);

						std::multimap<std::string, automata::ClockConstraint> zone =
							zones::get_fulfilled_clock_constraints(clock_constraints, s.clock, s.clock_valuation);

						return PlantZoneState<Location>(s.location,
														s.clock,
														zone,
														K);
					} else {
						const ATAState<ConstraintSymbolType> &s = std::get<ATAState<ConstraintSymbolType>>(w);

						std::multimap<std::string, automata::ClockConstraint> zone =
							zones::get_fulfilled_clock_constraints(clock_constraints, "", s.clock_valuation);

						return ATAZoneState<ConstraintSymbolType>(s.location,
																  zone,
																  K);
					}
				});
			abs.push_back(abs_i);
		}
		assert(is_valid_canonical_word(abs, 2 * K + 1));

		return abs;
	}
	
}

/** Print an ABRegionSymbol. */
template <typename LocationT, typename ConstraintSymbolType>
std::ostream &
operator<<(std::ostream &os, const search::ABRegionSymbol<LocationT, ConstraintSymbolType> &symbol)
{
	std::visit([&os](const auto &v) { os << v; }, symbol);
	return os;
}

/** Print a set of ABRegionSymbols (a letter of a CanonicalABWord). */
template <typename LocationT, typename ConstraintSymbolType>
std::ostream &
operator<<(std::ostream                                                            &os,
           const std::set<search::ABRegionSymbol<LocationT, ConstraintSymbolType>> &word)
{
	if (word.empty()) {
		os << "{}";
		return os;
	}
	os << "{ ";
	bool first = true;
	for (const auto &symbol : word) {
		if (!first) {
			os << ", ";
		} else {
			first = false;
		}
		os << symbol;
	}
	os << " }";
	return os;
}

/** Print a CanonicalABWord. */
template <typename LocationT, typename ConstraintSymbolType>
std::ostream &
operator<<(
  std::ostream                                                                         &os,
  const std::vector<std::set<search::ABRegionSymbol<LocationT, ConstraintSymbolType>>> &word)
{
	if (word.empty()) {
		os << "[]";
		return os;
	}
	os << "[ ";
	bool first = true;
	for (const auto &symbol : word) {
		if (!first) {
			os << ", ";
		} else {
			first = false;
		}
		os << symbol;
	}
	os << " ]";
	return os;
}

/** Print a vector of CanonicalABWords. */
template <typename LocationT, typename ConstraintSymbolType>
std::ostream &
operator<<(std::ostream                                                                &os,
           const std::vector<search::CanonicalABWord<LocationT, ConstraintSymbolType>> &ab_words)
{
	if (ab_words.empty()) {
		os << "{}";
		return os;
	}
	os << "{ ";
	bool first = true;
	for (const auto &ab_word : ab_words) {
		if (!first) {
			os << ", ";
		} else {
			first = false;
		}
		os << ab_word;
	}
	os << " }";
	return os;
}

/** Print a multimap of (symbol, CanonicalABWord). */
template <typename ActionT, typename LocationT, typename ConstraintSymbolType>
std::ostream &
operator<<(
  std::ostream                                                                           &os,
  const std::multimap<ActionT, search::CanonicalABWord<LocationT, ConstraintSymbolType>> &ab_words)
{
	if (ab_words.empty()) {
		os << "{}";
		return os;
	}
	os << "{ ";
	bool first = true;
	for (const auto &[symbol, ab_word] : ab_words) {
		if (!first) {
			os << ", ";
		} else {
			first = false;
		}
		os << "(" << symbol << ", " << ab_word << ")";
	}
	os << " }";
	return os;
}

/** Print a next canonical word along with its region index and action. */
template <typename LocationT, typename ActionType, typename ConstraintSymbolType>
std::ostream &
operator<<(std::ostream                                                               &os,
           const std::tuple<RegionIndex,
                            ActionType,
                            search::CanonicalABWord<LocationT, ConstraintSymbolType>> &ab_word)
{
	os << "(" << std::get<0>(ab_word) << ", " << std::get<1>(ab_word) << ", " << std::get<2>(ab_word)
	   << ")";
	return os;
}

/** Print a vector of next canonical words. */
template <typename LocationT, typename ActionType, typename ConstraintSymbolType>
std::ostream &
operator<<(
  std::ostream &os,
  const std::vector<
    std::tuple<RegionIndex, ActionType, search::CanonicalABWord<LocationT, ConstraintSymbolType>>>
    &ab_words)
{
	if (ab_words.empty()) {
		os << "{}";
		return os;
	}
	os << "{ ";
	bool first = true;
	for (const auto &ab_word : ab_words) {
		if (!first) {
			os << ", ";
		} else {
			first = false;
		}
		os << ab_word;
	}
	os << " }";
	return os;
}

/** Print a set of CanonicalABWords. */
template <typename LocationT, typename ConstraintSymbolType>
std::ostream &
operator<<(std::ostream                                                             &os,
           const std::set<search::CanonicalABWord<LocationT, ConstraintSymbolType>> &ab_words)
{
	if (ab_words.empty()) {
		os << "{}";
		return os;
	}
	os << "{ ";
	bool first = true;
	for (const auto &ab_word : ab_words) {
		if (!first) {
			os << ", ";
		} else {
			first = false;
		}
		os << ab_word;
	}
	os << " }";
	return os;
}

} // namespace tacos::search

namespace fmt {

template <typename LocationT, typename ConstraintSymbolType>
struct formatter<tacos::search::ABRegionSymbol<LocationT, ConstraintSymbolType>> : ostream_formatter
{
};

} // namespace fmt
