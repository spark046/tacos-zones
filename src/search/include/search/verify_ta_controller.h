#pragma once

#include "search.h"
#include "search_tree.h"
#include "create_controller.h"
#include "canonical_word.h"
#include "automata/ta.h"
#include "mtl/MTLFormula.h"
#include "mtl_ata_translation/translator.h"

namespace tacos::search {

using automata::ta::TimedAutomaton;

/** Creates a synchronous product between a Plant TA and a Controller TA */
template <typename LocationT, typename ActionType, typename ConstraintSymbolType>
TimedAutomaton<std::pair<automata::ta::Location<LocationT>, automata::ta::Location<std::set<CanonicalABWord<automata::ta::Location<LocationT>, ConstraintSymbolType>>>>, ActionType>
create_product(const TimedAutomaton<LocationT, ActionType> &ta,
			   const TimedAutomaton<std::set<search::CanonicalABWord<automata::ta::Location<LocationT>, ConstraintSymbolType>>, ActionType> &controller)
{
	//Saving mouthfuls
	using Controller_Location = std::set<search::CanonicalABWord<automata::ta::Location<LocationT>, ConstraintSymbolType>>;

	//For Product TA
	using LocationType = std::pair<automata::ta::Location<LocationT>, automata::ta::Location<Controller_Location>>;
	using TA = TimedAutomaton<LocationType, ActionType>;
	using Location = automata::ta::Location<LocationType>;
	using Transition = automata::ta::Transition<LocationType, ActionType>;

	std::set<Location> locations;
	std::set<ActionType> alphabet;
	std::set<Location> accepting_locations;
	std::set<std::string> clocks;
	std::vector<Transition> transitions;

	//Get cartesian product of all locations
	for(const auto &ta_location : ta.get_locations()) {
		for(const auto &controller_location : controller.get_locations()) {
			locations.insert(Location{std::make_pair(ta_location, controller_location)});
		}
	}

	//Get accepting locations
	for(const auto &ta_location : ta.get_final_locations()) {
		for(const auto &controller_location : controller.get_final_locations()) {
			accepting_locations.insert(Location{std::make_pair(ta_location, controller_location)});
		}
	}

	//Get alphabet, although alphabet of controller should be subset of Plant's alphabet
	std::set_union(ta.get_alphabet().begin(), ta.get_alphabet().end(),
				   controller.get_alphabet().begin(), controller.get_alphabet().end(),
				   inserter(alphabet, alphabet.end()));
	
	//Get Clocks
	std::set_union(ta.get_clocks().begin(), ta.get_clocks().end(),
				   controller.get_clocks().begin(), controller.get_clocks().end(),
				   inserter(clocks, clocks.end()));

	//Get transitions
	for(const auto &location : locations) {
		auto [ta_trans_curr, ta_trans_end] =
			ta.get_transitions().equal_range(location.get().first);
		auto [controller_trans_curr, controller_trans_end] =
			controller.get_transitions().equal_range(location.get().second);

		//No transitions from this location for neither Plant nor Controller
		if(ta_trans_curr == ta_trans_end || controller_trans_curr == controller_trans_end) {
			continue;
		}

		//Check transitions for all actions
		for(const auto &action : alphabet) {
			std::set<automata::ta::Transition<LocationT, ActionType>> ta_transitions;
			std::set<automata::ta::Transition<Controller_Location, ActionType>> controller_transitions;

			//Check Plant TA
			for(; ta_trans_curr != ta_trans_end; ta_trans_curr++) {
				if(ta_trans_curr->second.get_label() == action) {
					ta_transitions.insert(ta_trans_curr->second);
				}
			}

			//Check Controller TA
			for(; controller_trans_curr != controller_trans_end; controller_trans_curr++) {
				if(controller_trans_curr->second.get_label() == action) {
					controller_transitions.insert(controller_trans_curr->second);
				}
			}

			for(const auto &ta_trans : ta_transitions) {
				for(const auto &controller_trans : controller_transitions) {
					std::multimap<std::string, automata::ClockConstraint> guards = ta_trans.get_guards();
					guards.insert(controller_trans.get_guards().begin(), controller_trans.get_guards().end());

					//If the guards aren't satisfiable, then this transition would never be able to be taken anyway
					if(!automata::is_satisfiable(guards)) {
						continue;
					}

					std::set<std::string> resets;

					std::set_union(ta_trans.get_reset().begin(), ta_trans.get_reset().end(),
								   controller_trans.get_reset().begin(), controller_trans.get_reset().end(),
								   inserter(resets, resets.end()));

					transitions.push_back(Transition(
						Location{std::make_pair(ta_trans.get_source(), controller_trans.get_source())},
						action,
						Location{std::make_pair(ta_trans.get_target(), controller_trans.get_target())},
						guards,
						resets
					));
				}
			}
		}
	}

	return TA{
		locations,
		alphabet,
		Location{std::make_pair(ta.get_initial_location(), controller.get_initial_location())},
		accepting_locations,
		clocks,
		transitions
	};
}

/** Verifies a controller for TAs by constructing the synchronous product between the Plant TA and the controller TA, and then
 * making every action an environment action, and then checking whether the root is labelled TOP.
 * 
 * @param ta The plant TA
 * @param controller The TA of the controller
 * @return True if the controller is correct, false otherwise
 */
template <typename LocationT, typename ActionType, typename ConstraintSymbolType = ActionType>
bool
verify_ta_controller(const TimedAutomaton<LocationT, ActionType> &ta,
					 const TimedAutomaton<std::set<search::CanonicalABWord<automata::ta::Location<LocationT>, ConstraintSymbolType>>, ActionType> &controller,
					 const logic::MTLFormula<ConstraintSymbolType> &spec,
					 RegionIndex K)
{
	//Saving mouthfuls
	using Controller_Location = std::set<search::CanonicalABWord<automata::ta::Location<LocationT>, ConstraintSymbolType>>;

	//For Product TA
	using LocationType = std::pair<automata::ta::Location<LocationT>, automata::ta::Location<Controller_Location>>;
	using TA = TimedAutomaton<LocationType, ActionType>;
	using Location = automata::ta::Location<LocationType>;

	//~~~~~~~1. Create synchronous product and build the search tree~~~~~~~~~

	//1.1 Make every action an environment action
	std::set<ActionType> actions;
	std::set_union(ta.get_alphabet().begin(), ta.get_alphabet().end(),
				   controller.get_alphabet().begin(), controller.get_alphabet().end(),
				   inserter(actions, end(actions)));

	//1.2 Create synchronous product
	TA product = create_product(ta, controller);

	//1.3 Build Search Tree
	//Empty ATA
	std::set<logic::AtomicProposition<ConstraintSymbolType>> ata_actions;
	ata_actions.insert(actions.begin(), actions.end());

	auto ata = mtl_ata_translation::translate(spec, ata_actions);
	TreeSearch<Location, ActionType, ConstraintSymbolType> search{
		&product,
		&ata,
		{},
		actions,
		K
	};

	search.build_tree(true);

	return search.get_root()->label == NodeLabel::TOP;
}

/** Print a synchronous product's location. */
template <typename LocationT, typename ConstraintSymbolType>
std::ostream &
operator<<(std::ostream &os, const std::pair<
	automata::ta::Location<LocationT>,
	automata::ta::Location<std::set<search::CanonicalABWord<automata::ta::Location<LocationT>, ConstraintSymbolType>>>> &location)
{
	os << "(" << location.first << ", " << location.second << ")";
	return os;
}

} //tacos::search

namespace fmt {

template <typename LocationT, typename ConstraintSymbolType>
struct formatter<std::pair<
	tacos::automata::ta::Location<LocationT>,
	tacos::automata::ta::Location<std::set<tacos::search::CanonicalABWord<tacos::automata::ta::Location<LocationT>, ConstraintSymbolType>>>>> : ostream_formatter
{
};

} // fmt