/***************************************************************************
 *  ata.h - Alternating Timed Automata
 *
 *  Created: Fri 05 Jun 2020 10:58:27 CEST 10:58
 *  Copyright  2020  Till Hofmann <hofmann@kbsg.rwth-aachen.de>
 *  SPDX-License-Identifier: LGPL-3.0-or-later
 ****************************************************************************/

#ifndef SRC_AUTOMATA_INCLUDE_AUTOMATA_ATA_H
#define SRC_AUTOMATA_INCLUDE_AUTOMATA_ATA_H

#include "ata_formula.h"
#include "automata.h"

#include <fmt/ostream.h>

#include <experimental/iterator>
#include <stdexcept>
#include <string>
#include <vector>

/// Alternating timed automata
namespace tacos::automata::ata {

/** A symbol-time pair. */
template <typename SymbolT = std::string>
using TimedATASymbol = std::pair<SymbolT, Time>;
/** An ATA timed word is a sequence of symbol-time pairs. */
template <typename SymbolT = std::string>
using TimedATAWord = std::vector<TimedATASymbol<SymbolT>>;

/// Thrown if the wrong ATA transition type is attempted
class WrongTransitionTypeException : public std::logic_error
{
public:
	/** Constructor.
	 * @param what The error message
	 */
	WrongTransitionTypeException(const std::string &what);
};

/// Thrown if a transition with a negative time delta is attempted
class NegativeTimeDeltaException : public std::logic_error
{
public:
	/** Constructor.
	 * @param time_delta The negative time difference to warn about
	 */
	NegativeTimeDeltaException(Time time_delta);
};

/** An ATA configuration is a set of ATA states.
 *
 * An ATA configuration is defined by a set of states, which in turn are pairs of an ATA location
 * and a clock valuation of the ATA's single clock. */
template <typename LocationT>
using Configuration = std::set<State<LocationT>>;

template <typename LocationT>
using ZoneConfiguration = std::set<ZoneState<LocationT>>;

/** A single step in a run of an ATA. */
template <typename SymbolT>
using RunStep = std::variant<SymbolT, Time>;

/** One component of an ATA run, i.e., a single step and the resulting configuration */
template <typename LocationT, typename SymbolT>
using RunComponent = std::pair<RunStep<SymbolT>, Configuration<LocationT>>;

/** A run is a sequence of steps and the corresponding resulting configurations. */
template <typename LocationT, typename SymbolT>
using Run = std::vector<RunComponent<LocationT, SymbolT>>;

template <typename LocationT, typename SymbolT>
class AlternatingTimedAutomaton;

template <typename LocationT, typename SymbolT>
class Transition;

template <typename LocationT, typename SymbolT>
std::ostream &operator<<(std::ostream                                               &os,
                         const tacos::automata::ata::Transition<LocationT, SymbolT> &transition);

template <typename LocationT, typename SymbolT>
std::ostream &
operator<<(std::ostream                                                              &os,
           const tacos::automata::ata::AlternatingTimedAutomaton<LocationT, SymbolT> &ata);

/** Print a configuration to an ostream.
 * @param os The ostream to print to
 * @param configuration The configuration to print
 * @return A reference to the ostream
 */
template <typename LocationT>
std::ostream &operator<<(std::ostream                                         &os,
                         const tacos::automata::ata::Configuration<LocationT> &configuration);

/** Print a run to an ostream.
 * @param os The ostream to print to
 * @param run The run to print
 * @return A reference to the ostream
 */
template <typename LocationT, typename SymbolT>
std::ostream &operator<<(std::ostream                                        &os,
                         const tacos::automata::ata::Run<LocationT, SymbolT> &run);

template <typename LocationT, typename SymbolT>
bool operator<(const Transition<LocationT, SymbolT> &first,
               const Transition<LocationT, SymbolT> &second);

/// A transition of an alternating timed automaton
template <typename LocationT, typename SymbolT>
class Transition
{
public:
	friend class AlternatingTimedAutomaton<LocationT, SymbolT>;
	/** Print a Transition to an ostream
	 * @param os The ostream to print to
	 * @param transition The Transition to print
	 * @return A reference to the ostream
	 */
	// clang-format off
	friend std::ostream &operator<< <>(std::ostream &os, const Transition &transition);
	// clang-format on

	/** Compare two transitions.
	 * @param first The first Transition to compare
	 * @param second The second Transition to compare
	 * @return true if the first Transition is smaller than the second
	 */
	// clang-format off
	friend bool operator< <>(const Transition &first, const Transition &second);
	// clang-format on

	/** Delete the copy constructor, as we cannot copy the formula pointer. */
	Transition(const Transition &) = delete;

	/** Move constructor */
	Transition(Transition &&) = default;

	/** Constructor.
	 * @param source The source location of the transition
	 * @param symbol The symbol to read with this transition
	 * @param formula The formula that is used to determine the configuration after this transition
	 */
	Transition(const LocationT                    &source,
	           const SymbolT                      &symbol,
	           std::unique_ptr<Formula<LocationT>> formula);

	std::set<automata::ClockConstraint>
	get_clock_constraints() const
	{
		return formula_->get_clock_constraints();
	}

	/** Gets the symbol to take this transition */
	SymbolT
	get_symbol() const {
		return symbol_;
	}

	/**
	 * Calculates a minimal model for this transition from a state w.r.t. the Zone of the state.
	 * (The location of the state is already implicitly part of this Transition)
	 * 
	 * The first minimal model from the set of all minimal models is taken
	 * 
	 * @param z The Zone_slice of the state.
	 * @return A Minimal Model, which consist of a set of ZoneStates, which have a location and Zone_slice => set::(location, Zone)
	 */
	std::set<ZoneConfiguration<LocationT>>
	get_minimal_models(zones::Zone_slice z) const
	{
		return formula_->get_minimal_models(z);
	}

public:
	/// The source location of the transition
	const LocationT source_;
	/// The symbol this transition can fire on
	const SymbolT symbol_;

private:
	std::unique_ptr<Formula<LocationT>> formula_;
};

/// An alternating timed automaton.
template <typename LocationT, typename SymbolT>
class AlternatingTimedAutomaton
{
public:
	AlternatingTimedAutomaton() = delete;
	/** Constructor.
	 * @param alphabet The set of symbols used by the automaton
	 * @param initial_location The initial location that determines the initial state
	 * @param final_locations The locations where the automaton is accepting
	 * @param transitions The set of transitions used by the automaton
	 * @param sink_location If this optional location is given, use it as sink if no other transition
	 * is possible.
	 */
	AlternatingTimedAutomaton(const std::set<SymbolT>                 &alphabet,
	                          const LocationT                         &initial_location,
	                          const std::set<LocationT>               &final_locations,
	                          std::set<Transition<LocationT, SymbolT>> transitions,
	                          std::optional<LocationT>                 sink_location = std::nullopt);

	/** Get the initial configuration.
	 * @return The initial configuration of the automaton.
	 */
	[[nodiscard]] Configuration<LocationT> get_initial_configuration() const;

	/** Get the automaton's alphabet. */
	[[nodiscard]] const std::set<SymbolT> &
	get_alphabet() const
	{
		return alphabet_;
	}

	[[nodiscard]] const std::set<Transition<LocationT, SymbolT>> &
	get_transitions() const
	{
		return transitions_;
	}

	const std::optional<LocationT> &
	get_sink_location() const
	{
		return sink_location_;
	}

	/** Compute the resulting configurations after making a symbol step.
	 * @param start_states The starting configuration
	 * @param symbol The symbol to read
	 * @return The configurations after making the symbol step
	 */
	std::set<Configuration<LocationT>> make_symbol_step(const Configuration<LocationT> &start_states,
	                                                    const SymbolT                  &symbol) const;

	/** Compute the resulting configurations and all constraints after making a symbol step.
	 * @param start_states The starting configuration
	 * @param symbol The symbol to read
	 * @return A pair consisting of the configurations after making the symbol step and a set of clock constraints
	 */
	std::pair<std::set<Configuration<LocationT>>, std::set<ClockConstraint>> make_symbol_step_with_constraints(const Configuration<LocationT> &start_states,
	                                                    const SymbolT                  &symbol) const;

	/** Compute the resulting run after reading a symbol.
	 * @param runs The valid runs resulting from reading previous symbols
	 * @param symbol The symbol to read
	 * @return The run appended with the resulting configuration
	 */
	std::vector<Run<LocationT, SymbolT>>
	make_symbol_transition(const std::vector<Run<LocationT, SymbolT>> &runs,
	                       const SymbolT                              &symbol) const;

	/** Compute the resulting configuration after progressing the time.
	 * @param start The starting configuration
	 * @param time The time difference to add to the automaton's clock
	 * @return The configuration after making the time step
	 */
	Configuration<LocationT> make_time_step(const Configuration<LocationT> &start,
	                                        const Time                     &time) const;

	/** Compute the resulting run after progressing the time.
	 * @param runs The valid runs resulting from reading previous symbols
	 * @param time The time difference to add to the automaton's clock
	 * @return The run augmented with the new configuration
	 */
	std::vector<Run<LocationT, SymbolT>>
	make_time_transition(const std::vector<Run<LocationT, SymbolT>> &runs, const Time &time) const;

	/** Check if the given configuration is accepting.
	 * @param configuration The configuration to check
	 * @return true if the configuration is an accepting configuration of the ATA
	 */
	[[nodiscard]] bool
	is_accepting_configuration(const Configuration<LocationT> &configuration) const;

	/** Check if the ATA accepts a timed word.
	 * @param word The timed word to check
	 * @return true if the given word is accepted
	 */
	[[nodiscard]] bool accepts_word(const TimedATAWord<SymbolT> &word) const;

	/** Print an AlternatingTimedAutomaton to an ostream
	 * @param os The ostream to print to
	 * @param ata The AlternatingTimedAutomaton to print
	 * @return A reference to the ostream
	 */
	// clang-format off
	friend std::ostream &
	operator<< <>(std::ostream &os, const AlternatingTimedAutomaton &ata);
	// clang-format on

	std::set<automata::ClockConstraint>
	get_clock_constraints() const
	{
		std::set<automata::ClockConstraint> ret = {};

		for(auto iter1 = transitions_.begin(); iter1 != transitions_.end(); iter1++)
		{
			std::set<automata::ClockConstraint> curr_set = iter1->get_clock_constraints();
			ret.insert(curr_set.begin(), curr_set.end());
		}

		return ret;
	}

	/**
	 * Get a multimap of all clock constraints from a specific configuration
	 */
	std::set<automata::ClockConstraint>
	get_clock_constraints(const Configuration<LocationT> &configuration) const
	{
		std::set<automata::ClockConstraint> ret = {};

		//TODO: Double for Loop. Can this be more efficient?
		for(auto iter1 = transitions_.begin(); iter1 != transitions_.end(); iter1++)
		{
			if(std::any_of(configuration.begin(), configuration.end(), [&iter1](const auto &state) {
				return state.location == iter1->source_;
			})) {
				std::set<automata::ClockConstraint> curr_set = iter1->get_clock_constraints();
				ret.insert(curr_set.begin(), curr_set.end());
			}
		}

		return ret;
	}

private:
	std::set<std::set<State<LocationT>>> get_minimal_models(Formula<LocationT> *formula,
	                                                        ClockValuation      v) const;

	const std::set<SymbolT>                        alphabet_;
	const LocationT                                initial_location_;
	const std::set<LocationT>                      final_locations_;
	const std::set<Transition<LocationT, SymbolT>> transitions_;
	const std::optional<LocationT>                 sink_location_;
};

} // namespace tacos::automata::ata

namespace fmt {

template <typename LocationT, typename SymbolT>
struct formatter<tacos::automata::ata::Transition<LocationT, SymbolT>> : ostream_formatter
{
};

template <typename LocationT, typename SymbolT>
struct formatter<tacos::automata::ata::AlternatingTimedAutomaton<LocationT, SymbolT>>
: ostream_formatter
{
};

template <typename LocationT, typename SymbolT>
struct formatter<tacos::automata::ata::Run<LocationT, SymbolT>> : ostream_formatter
{
};

} // namespace fmt

#include "ata.hpp"

#endif /* ifndef SRC_AUTOMATA_INCLUDE_AUTOMATA_ATA_H */
