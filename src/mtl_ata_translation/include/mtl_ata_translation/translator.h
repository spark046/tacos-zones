/***************************************************************************
 *  translator.h - Translate an MTL formula into an ATA
 *
 *  Created: Thu 18 Jun 2020 11:06:49 CEST 11:06
 *  Copyright  2020  Till Hofmann <hofmann@kbsg.rwth-aachen.de>
 ****************************************************************************/

/*  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation; either version 2 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU Library General Public License for more details.
 *
 *  Read the full text in the LICENSE.GPL file in the doc directory.
 */

#pragma once

#include <mtl/MTLFormula.h>
#include <ta/ata.h>

namespace mtl_ata_translation {

// TODO We should deduce the ActionType from the MTLFormula template type.
using ActionType = std::string;

automata::ata::AlternatingTimedAutomaton<logic::MTLFormula<ActionType>,
                                         logic::AtomicProposition<std::string>>
translate(const logic::MTLFormula<ActionType> &formula);

} // namespace mtl_ata_translation