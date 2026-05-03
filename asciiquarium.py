#!/usr/bin/env python3

#############################################################################
# Asciiquarium - An aquarium animation in ASCII art (Python/Curses Version)
#
# Based on the original Perl script by Kirk Baucom.
#
# This program displays an aquarium/sea animation using ASCII art.
# It requires the 'curses' module, which is standard on Unix-like systems.
#
# Original Perl version: http://robobunny.com/projects/asciiquarium
#############################################################################
# Original Author:
#   Kirk Baucom <kbaucom@schizoid.com>
#
# Contributors (to original Perl):
#   Joan Stark: most of the ASCII art
#   Claudio Matsuoka: improved marine biodiversity
#
# License:
#
# Copyright (C) 2003 Kirk Baucom (kbaucom@schizoid.com)
#
# This program is free software; you can redistribute it and/or
# modify it under the terms of the GNU General Public License
# as published by the Free Software Foundation; either version 2
# of the License, or (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
#############################################################################

"""Thin entry point. Re-exports cli_entry so the pyproject.toml
console-script `asciiquarium = "asciiquarium:cli_entry"` keeps working,
and `python3 asciiquarium.py` continues to launch the program.

Public symbols from the split engine are re-exported here so external
imports (`import asciiquarium; asciiquarium.Animation(...)`) and the
existing test suite keep working without each having to chase the new
module layout.
"""

from animation import Animation
from cli import cli_entry, cleanup, main, parse_args, signal_handler
from constants import (
    BASE_FISH_PALETTE, COLOR_CHAR_MAP, COLOR_MAP, DEPTH,
    EXTENDED_COLOR_MAP, TICK_RATE, VERSION,
)
from creatures import (
    RANDOM_OBJECT_POOL,
    bubble_collision, create_all_fish, create_all_seaweed, create_big_fish,
    create_big_fish_1, create_big_fish_2, create_bubble, create_castle,
    create_environment, create_fish, create_fish_entity, create_monster,
    create_monster_entity, create_new_fish_entity, create_new_monster_entity,
    create_old_fish_entity, create_old_monster_entity, create_random_object,
    create_seaweed, create_ship, create_shark, create_splat, create_whale,
    fish_collision, fish_update, get_new_fish_data, get_new_monster_data,
    get_old_fish_data, get_old_monster_data, rand_color_mask, shark_death,
)
from entity import Entity, shape_dimensions


if __name__ == "__main__":
    cli_entry()
