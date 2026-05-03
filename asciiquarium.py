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

import curses
import time
import random
import argparse
import signal
import sys
import atexit

from assets import (
    WATER_LINE_SEGMENTS,
    CASTLE_SHAPE, CASTLE_MASK,
    SPLAT_SHAPES,
    SHARK_SHAPES, SHARK_MASKS,
    SHIP_SHAPES, SHIP_MASKS,
    WHALE_SHAPES, WHALE_MASKS, WATER_SPOUT_FRAMES,
    NEW_MONSTER_FRAMES, NEW_MONSTER_MASKS,
    OLD_MONSTER_FRAMES, OLD_MONSTER_MASKS,
    BIG_FISH_1_SHAPES, BIG_FISH_1_MASKS,
    BIG_FISH_2_SHAPES, BIG_FISH_2_MASKS,
    NEW_FISH_DATA, OLD_FISH_DATA,
)

VERSION = "1.1 (Python)"
NEW_FISH = True
NEW_MONSTER = True

# Velocity values across the codebase (fish vx ~0.25–2.25, shark/monster 2.0,
# whale/ship 1.0, bubble vy=-1) are calibrated for the Perl original, which
# called animate() at 10 Hz via halfdelay(1). Scale by elapsed real time so
# Python's --fps choice doesn't change visible speeds.
TICK_RATE = 10.0  # "Perl ticks" per real second

# --- Color Definitions ---
# Map color names/chars to curses color constants and pair indices
COLOR_MAP = {
    'black': curses.COLOR_BLACK,
    'red': curses.COLOR_RED,
    'green': curses.COLOR_GREEN,
    'yellow': curses.COLOR_YELLOW,
    'blue': curses.COLOR_BLUE,
    'magenta': curses.COLOR_MAGENTA,
    'cyan': curses.COLOR_CYAN,
    'white': curses.COLOR_WHITE,
}

# Character mappings used in color masks
# Lowercase = normal intensity, Uppercase = bold/bright
COLOR_CHAR_MAP = {
    # Char: (curses_color, bold_attribute)
    'x': (curses.COLOR_BLACK, curses.A_NORMAL), # Default/Black
    'r': (curses.COLOR_RED, curses.A_NORMAL),
    'g': (curses.COLOR_GREEN, curses.A_NORMAL),
    'y': (curses.COLOR_YELLOW, curses.A_NORMAL),
    'b': (curses.COLOR_BLUE, curses.A_NORMAL),
    'm': (curses.COLOR_MAGENTA, curses.A_NORMAL),
    'c': (curses.COLOR_CYAN, curses.A_NORMAL),
    'w': (curses.COLOR_WHITE, curses.A_NORMAL),
    'R': (curses.COLOR_RED, curses.A_BOLD),
    'G': (curses.COLOR_GREEN, curses.A_BOLD),
    'Y': (curses.COLOR_YELLOW, curses.A_BOLD),
    'B': (curses.COLOR_BLUE, curses.A_BOLD),
    'M': (curses.COLOR_MAGENTA, curses.A_BOLD),
    'C': (curses.COLOR_CYAN, curses.A_BOLD),
    'W': (curses.COLOR_WHITE, curses.A_BOLD),
}

# Extra fish-color shades available on 256-color terminals. The chars are
# kept distinct from any digit/letter that appears in mask templates so
# they can be used as random substitutes for 1-9 without collision.
EXTENDED_COLOR_MAP = {
    # Char: xterm-256 index
    'o': 208,  # orange
    'p': 213,  # pink
    'l': 154,  # lime
    't': 51,   # bright teal/cyan
    'P': 165,  # purple
    'O': 220,  # gold
}

BASE_FISH_PALETTE = ['c', 'C', 'r', 'R', 'y', 'Y', 'b', 'B', 'g', 'G', 'm', 'M']

# Z depth at which certain items occur
DEPTH = {
    # no gui yet
    'guiText': 0,
    'gui': 1,

    # under water
    'shark': 2,
    'fish_start': 3,
    'fish_end': 20,
    'seaweed': 21,
    'castle': 22,

    # waterline - adjusted slightly for typical terminal line spacing
    'water_line3': 2,
    'water_gap3': 3,
    'water_line2': 4,
    'water_gap2': 5,
    'water_line1': 6,
    'water_gap1': 7,
    'water_line0': 8,
    'water_gap0': 9,
}

# --- Entity Class ---
class Entity:
    def __init__(self, name="", type="", shape=None, color_map=None,
                 pos=(0, 0, 0), velocity=(0, 0, 0), anim_speed=0.0,
                 default_color_char='c', die_offscreen=False,
                 die_time=None, die_frame=None, death_cb=None, death_cb_args=None,
                 update_cb=None, update_cb_args=None,
                 coll_handler=None, physical=False, transparent_char=' ',
                 auto_trans=False):

        self.name = name if name else f"{type}_{random.randint(1000, 9999)}"
        self.type = type
        self.x, self.y, self.z = pos
        self.vx, self.vy, self.vz = velocity[:3] # Speed in x, y, z
        # Optional 4th velocity element is animation speed modifier.
        # Clamp to a small positive value so update() never divides by zero.
        modifier = velocity[3] if len(velocity) > 3 else 1.0
        self.anim_speed_modifier = modifier if modifier > 0 else 1.0

        self.shapes = shape if isinstance(shape, list) else [shape]
        self.color_maps = color_map if isinstance(color_map, list) else [color_map] * len(self.shapes)

        # Ensure color_maps length matches shapes length
        if len(self.color_maps) < len(self.shapes):
             self.color_maps.extend([self.color_maps[-1]] * (len(self.shapes) - len(self.color_maps)))

        # If auto_trans is on, preprocess each shape so only EXTERIOR
        # spaces (leading + trailing on each line) are transparent.
        # Interior spaces (between the first and last non-space char)
        # remain as ' ' and render opaquely. This stops back-layer
        # entities from showing characters through the silhouette of a
        # front-layer entity that overlaps it — the visible bug when
        # two fish swim past each other. The transformation is done
        # once at construction; auto_trans is consumed here.
        if auto_trans:
            self.shapes = [self._mark_exterior_transparent(s) for s in self.shapes]
            auto_trans = False
        self.auto_trans = auto_trans

        self.current_frame = 0
        self.anim_speed = anim_speed # Time between frames
        self.last_anim_time = time.monotonic()

        self.default_color_char = default_color_char.upper() if default_color_char.isupper() else default_color_char.lower()
        self.die_offscreen = die_offscreen
        self.die_time = die_time
        self.die_frame = die_frame # Die after this many animation frames shown
        self._frames_shown = 0
        self.death_cb = death_cb
        self.death_cb_args = death_cb_args if death_cb_args is not None else []
        self.update_cb = update_cb
        self.update_cb_args = update_cb_args if update_cb_args is not None else []
        self.coll_handler = coll_handler
        self.physical = physical # Can participate in collisions
        self.transparent_char = transparent_char
        # self.auto_trans was already set above, after possible consumption
        # via shape preprocessing.

        self.is_alive = True
        self._width = 0
        self._height = 0
        self._lines = []
        self._color_lines = []
        self._update_dimensions() # Initial calculation

        # For collision detection
        self.collisions = []

    @staticmethod
    def _mark_exterior_transparent(shape_str):
        """ Replace each line's leading and trailing spaces with '?'
        (the universal transparent char). Interior spaces keep being
        rendered as opaque, so a fish silhouette occludes whatever is
        behind it instead of letting characters bleed through. """
        if not shape_str:
            return shape_str
        out = []
        for line in shape_str.split('\n'):
            stripped_left = line.lstrip(' ')
            leading = len(line) - len(stripped_left)
            stripped = stripped_left.rstrip(' ')
            trailing = len(stripped_left) - len(stripped)
            out.append('?' * leading + stripped + '?' * trailing)
        return '\n'.join(out)

    def _update_dimensions(self):
        """ Recalculate dimensions based on the current frame's shape. """
        shape_str = self.shapes[self.current_frame]
        if not shape_str:
            self._width = 0
            self._height = 0
            self._lines = []
            self._color_lines = []
            return

        self._lines = shape_str.strip('\n').split('\n')
        self._height = len(self._lines)
        self._width = max(len(line) for line in self._lines) if self._lines else 0

        # Process color map for the current frame
        color_map_str = self.color_maps[self.current_frame]
        if color_map_str:
            self._color_lines = color_map_str.strip('\n').split('\n')
        else:
            self._color_lines = [] # No specific color map for this frame


    def get_shape_and_colors(self):
        """ Returns the lines and color lines for the current frame """
        return self._lines, self._color_lines

    def width(self):
        return self._width

    def height(self):
        return self._height

    def size(self):
         return (self._width, self._height)

    def position(self):
        return (self.x, self.y, self.z)

    def kill(self):
        self.is_alive = False

    def update(self, animation_instance, dt):
        """ Update entity state (position, animation frame, life status).

        `dt` is the real seconds elapsed since the last animate() call;
        velocities are interpreted in cells per Perl tick (1/TICK_RATE
        seconds), so movement is frame-rate independent.
        """
        if not self.is_alive:
            return

        # Use wall-clock for die_time (humans set it via time.time() + N
        # in the seaweed callback) but monotonic for the animation
        # interval check, which only cares about elapsed time.
        now_wall = time.time()
        now_mono = time.monotonic()

        # --- Life checks ---
        if self.die_time and now_wall >= self.die_time:
            self.kill()
            return
        if self.die_frame and self._frames_shown >= self.die_frame:
             self.kill()
             return

        # --- Animation Frame ---
        if len(self.shapes) > 1 and self.anim_speed > 0:
            if now_mono - self.last_anim_time >= (self.anim_speed / self.anim_speed_modifier):
                self.current_frame = (self.current_frame + 1) % len(self.shapes)
                self._update_dimensions()
                self.last_anim_time = now_mono
                self._frames_shown += 1

        # --- Movement (cells per Perl tick × real seconds × ticks/sec) ---
        step = dt * TICK_RATE
        self.x += self.vx * step
        self.y += self.vy * step

        # --- Offscreen Check ---
        if self.die_offscreen and self.is_offscreen(animation_instance.width, animation_instance.height):
             self.kill()
             return

        # --- Custom Update Callback ---
        if self.update_cb:
             # Pass self and the animation instance to the callback
             self.update_cb(self, animation_instance, *self.update_cb_args)

    def is_offscreen(self, screen_width, screen_height):
        """ Check if the entity is completely offscreen. """
        # Consider the entity's bounding box
        if (self.x + self.width()) <= 0 or self.x >= screen_width:
            return True
        if (self.y + self.height()) <= 0 or self.y >= screen_height:
            return True
        return False

    def handle_collisions(self, animation_instance):
        """ Call the collision handler if defined and collisions occurred. """
        if self.coll_handler and self.collisions:
             self.coll_handler(self, animation_instance)
        # Clear collisions for the next frame
        self.collisions = []


# --- Animation Class ---
class Animation:
    def __init__(self, stdscr, classic_mode=False, fps=20.0, use_color=True):
        self.stdscr = stdscr
        self.height, self.width = stdscr.getmaxyx()
        self.entities = []
        self.paused = False
        self.needs_redraw = True # Flag to force redraw after resize etc.
        self.classic_mode = classic_mode
        self.frame_delay = 1.0 / fps if fps > 0 else 0.05
        self.use_color = use_color and curses.has_colors()
        self._init_colors()
        self._last_term_size = (self.height, self.width)
        self._last_animate_time = time.monotonic()

    def _init_colors(self):
        """ Initialize curses color pairs (or fall back to monochrome). """
        self.color_pairs = {}
        self.fish_palette = list(BASE_FISH_PALETTE)
        if not self.use_color:
            # Monochrome fallback: every color char maps to A_NORMAL, bold for caps.
            for char in COLOR_CHAR_MAP:
                attr = curses.A_BOLD if char.isupper() else curses.A_NORMAL
                self.color_pairs[char] = attr
            self.color_pairs['default'] = curses.A_NORMAL
            return

        curses.start_color()
        curses.use_default_colors() # Allow use of default terminal background

        pair_num = 1 # Start from 1, 0 is reserved for default white on black
        for char, (fg, attr) in COLOR_CHAR_MAP.items():
             # Use -1 for default background
             try:
                 curses.init_pair(pair_num, fg, -1)
                 self.color_pairs[char] = curses.color_pair(pair_num) | attr
                 pair_num += 1
             except curses.error:
                 # Ran out of color pairs.
                 pass
             if pair_num > curses.COLOR_PAIRS - 1:
                 break

        # Add a default pair if needed (e.g., white on default bg)
        if 'default' not in self.color_pairs:
             try:
                  curses.init_pair(pair_num, curses.COLOR_WHITE, -1)
                  self.color_pairs['default'] = curses.color_pair(pair_num) | curses.A_NORMAL
                  pair_num += 1
             except curses.error:
                  self.color_pairs['default'] = curses.color_pair(0) # Fallback

        # 256-color enrichment: register extra shades and expose them in
        # the fish palette so rand_color_mask can pick them.
        if curses.COLORS >= 256:
            for char, color_idx in EXTENDED_COLOR_MAP.items():
                if pair_num > curses.COLOR_PAIRS - 1:
                    break
                try:
                    curses.init_pair(pair_num, color_idx, -1)
                    self.color_pairs[char] = curses.color_pair(pair_num)
                    self.fish_palette.append(char)
                    pair_num += 1
                except curses.error:
                    pass


    def get_color_attr(self, color_char):
         """ Get curses attribute for a color character, falling back to default. """
         return self.color_pairs.get(color_char, self.color_pairs.get(color_char.lower(), self.color_pairs['default']))

    def add_entity(self, entity):
        self.entities.append(entity)
        self.needs_redraw = True

    def remove_entity(self, entity):
        try:
            self.entities.remove(entity)
            self.needs_redraw = True
        except ValueError:
            pass # Entity already removed

    def get_entities_of_type(self, entity_type):
        return [e for e in self.entities if e.type == entity_type]

    def remove_all_entities(self):
        self.entities = []
        self.needs_redraw = True

    def update_term_size(self):
        """ Check and update terminal size. """
        new_height, new_width = self.stdscr.getmaxyx()
        if (new_height, new_width) != self._last_term_size:
            self.height = new_height
            self.width = new_width
            self._last_term_size = (new_height, new_width)
            curses.resizeterm(self.height, self.width)
            self.stdscr.clear()
            self.needs_redraw = True
            return True
        return False

    def check_collisions(self):
         """ Basic collision detection placeholder. """
         physical_entities = [e for e in self.entities if e.physical and e.is_alive]
         # Very simple example: Check shark teeth against fish
         teeth_list = [e for e in physical_entities if e.type == 'teeth']
         fish_list = [e for e in physical_entities if e.type == 'fish']

         if not teeth_list:
              return

         teeth = teeth_list[0] # Assuming only one teeth entity
         tx, ty, _ = map(int, teeth.position())

         for fish in fish_list:
              fx, fy, _ = map(int, fish.position())
              fw, fh = fish.width(), fish.height()
              # Simple point-in-rectangle check for the teeth hitting the fish bounding box
              if fx <= tx < fx + fw and fy <= ty < fy + fh:
                   # Add collision info to both entities (if they have handlers)
                   if fish.coll_handler:
                        fish.collisions.append(teeth)
                   if teeth.coll_handler:
                       teeth.collisions.append(fish)

         # More general collision detection (e.g., rect overlap) would go here
         # for i, e1 in enumerate(physical_entities):
         #    for e2 in physical_entities[i+1:]:
         #       # Check for overlap between e1 and e2 bounding boxes
         #       if self.check_overlap(e1, e2):
         #           if e1.coll_handler: e1.collisions.append(e2)
         #           if e2.coll_handler: e2.collisions.append(e1)

    # def check_overlap(self, e1, e2):
    #     """ Check if the bounding boxes of two entities overlap. """
    #     x1, y1, _ = map(int, e1.position())
    #     w1, h1 = e1.width(), e1.height()
    #     x2, y2, _ = map(int, e2.position())
    #     w2, h2 = e2.width(), e2.height()
    #     return not (x1 + w1 < x2 or x2 + w2 < x1 or y1 + h1 < y2 or y2 + h2 < y1)


    def animate(self):
        """ Update all entities. """
        if self.paused:
            return

        now = time.monotonic()
        dt = now - self._last_animate_time
        # Clamp dt so a long pause/stall doesn't teleport every entity.
        if dt > 0.5:
            dt = self.frame_delay
        self._last_animate_time = now

        # Update entities
        for entity in self.entities:
            entity.update(self, dt)

        # Perform collision detection *after* all updates
        self.check_collisions()

        # Handle collisions and remove dead entities
        dead_entities = []
        for entity in self.entities:
            if not entity.is_alive:
                dead_entities.append(entity)
            else:
                entity.handle_collisions(self) # Call collision handlers if needed


        # Process deaths and callbacks *after* iteration
        for entity in dead_entities:
            if entity.death_cb:
                entity.death_cb(entity, self, *entity.death_cb_args)
            self.remove_entity(entity) # Remove from list


    def draw_screen(self):
        """ Draw all entities onto the screen. """
        if not self.needs_redraw and not any(e.is_alive for e in self.entities):
             # Only redraw if flag is set or entities exist
             # This check is basic, might need refinement based on entity updates
             pass # Skip drawing if nothing changed? (Risky with animation)

        self.stdscr.erase() # Clear screen

        # Sort entities by Z depth for drawing (higher Z drawn first = further back)
        # Draw from back to front
        sorted_entities = sorted(self.entities, key=lambda e: e.z, reverse=True)

        for entity in sorted_entities:
            if not entity.is_alive:
                continue

            lines, color_lines = entity.get_shape_and_colors()
            start_x, start_y = int(entity.x), int(entity.y)

            for i, line in enumerate(lines):
                current_y = start_y + i
                if 0 <= current_y < self.height:
                    color_line = color_lines[i] if i < len(color_lines) else ""
                    default_attr = self.get_color_attr(entity.default_color_char)

                    for j, char in enumerate(line):
                        current_x = start_x + j
                        if 0 <= current_x < self.width:
                             # Skip transparent characters. '?' matches the
                             # original Perl Term::Animation convention where
                             # '?' is the default transparency marker; many of
                             # the imported ASCII assets (complex fish, sharks,
                             # whales, monsters, big fish) use '?' to mark
                             # cells outside the irregular silhouette.
                             if char == '?' or char == entity.transparent_char or (entity.auto_trans and char == ' '):
                                 continue

                             # Determine color/attribute
                             attr = default_attr
                             if j < len(color_line):
                                 color_char = color_line[j]
                                 if color_char != ' ' and color_char != '?': # Use '?' or space for default
                                     attr = self.get_color_attr(color_char)

                             # Draw the character
                             try:
                                  self.stdscr.addch(current_y, current_x, char, attr)
                                  # self.stdscr.addstr(current_y, current_x, char, attr) # Use addstr if drawing single chars causes issues
                             except curses.error:
                                  # Handle potential error writing to bottom-right corner
                                  pass

        self.stdscr.refresh()
        self.needs_redraw = False


    def _show_help(self):
        """ Pause and display a help overlay until any key is pressed. """
        was_paused = self.paused
        self.paused = True
        lines = [
            f"Asciiquarium v{VERSION}",
            "",
            "  q       quit",
            "  p       pause / resume",
            "  r       redraw / restart",
            "  h, ?    show this help",
            "",
            "Press any key to return.",
        ]
        box_w = max(len(line) for line in lines) + 4
        box_h = len(lines) + 2
        start_y = max(0, (self.height - box_h) // 2)
        start_x = max(0, (self.width - box_w) // 2)

        attr = self.get_color_attr('W')
        self.stdscr.erase()
        try:
            for i in range(box_h):
                row = start_y + i
                if row >= self.height:
                    break
                if i == 0 or i == box_h - 1:
                    text = "+" + "-" * (box_w - 2) + "+"
                else:
                    body = lines[i - 1]
                    text = "| " + body.ljust(box_w - 4) + " |"
                self.stdscr.addnstr(row, start_x, text, max(0, self.width - start_x), attr)
        except curses.error:
            pass
        self.stdscr.refresh()

        # Wait (blocking) for any key.
        self.stdscr.nodelay(False)
        try:
            self.stdscr.getch()
        except curses.error:
            pass
        finally:
            self.stdscr.nodelay(True)

        self.paused = was_paused
        self.needs_redraw = True

    MIN_WIDTH = 40
    MIN_HEIGHT = 15

    # Entity types that are anchored to screen geometry — they need to be
    # rebuilt on resize. Everything else (fish, shark, whale, monster,
    # big_fish, bubble, teeth, splat) is free-floating and can stay.
    _GEOMETRY_TYPES = {'waterline', 'seaweed'}
    _GEOMETRY_NAMES = {'castle'}

    def _populate(self):
        """ Create the static + initial random-object population. """
        create_environment(self)
        create_castle(self)
        create_all_seaweed(self)
        create_all_fish(self)
        RANDOM_OBJECT_POOL[random.randrange(len(RANDOM_OBJECT_POOL))](None, self)
        self.paused = False
        self.needs_redraw = True

    def _rebuild_geometry(self):
        """ Resize-friendly partial reset.

        Drop only the entities that depend on terminal dimensions
        (water lines, castle, seaweed) and rebuild them at the new size.
        Cull any free-floating entity that's now wholly off-screen so it
        doesn't sit in limbo with die_offscreen=True still pending.
        """
        kept = []
        for e in self.entities:
            if e.type in self._GEOMETRY_TYPES or e.name in self._GEOMETRY_NAMES:
                continue  # discard
            if e.is_offscreen(self.width, self.height):
                continue  # was on the old screen, no longer on this one
            kept.append(e)
        self.entities = kept
        create_environment(self)
        create_castle(self)
        create_all_seaweed(self)
        # Top up fish if the new (larger) terminal warrants more.
        target = max(1, ((self.height - 9) * self.width) // 350)
        current = sum(1 for e in self.entities if e.type == 'fish')
        for _ in range(max(0, target - current)):
            create_fish(None, self)
        self.needs_redraw = True

    def _too_small(self):
        return self.height < self.MIN_HEIGHT or self.width < self.MIN_WIDTH

    def _show_too_small(self):
        self.stdscr.erase()
        msg = (f"terminal {self.width}x{self.height} is too small "
               f"(need >= {self.MIN_WIDTH}x{self.MIN_HEIGHT})")
        try:
            self.stdscr.addnstr(0, 0, msg[:max(0, self.width - 1)],
                                max(0, self.width - 1))
            self.stdscr.addnstr(1, 0, "press q to quit, resize to continue",
                                max(0, self.width - 1))
        except curses.error:
            pass
        self.stdscr.refresh()

    def run(self):
        """ Main animation loop. """
        global NEW_FISH, NEW_MONSTER # Allow modification based on classic mode

        # Set classic mode flags if specified
        if self.classic_mode:
            NEW_FISH = False
            NEW_MONSTER = False

        if not self._too_small():
            self._populate()

        self.stdscr.nodelay(True) # Make getch non-blocking

        last_time = time.monotonic()
        frame_delay = self.frame_delay # Configured via --fps (default 20)

        while True:
            # --- Poll terminal size every frame.
            # Some hosts (notably tmux panes) don't reliably deliver
            # KEY_RESIZE through getch(), so we don't depend on the key
            # alone — we ask the screen directly each tick. update_term_size()
            # returns True only when dimensions actually changed, so this
            # is cheap.
            if self.update_term_size():
                if self._too_small():
                    self.remove_all_entities()
                elif not self.entities:
                    self._populate()
                else:
                    self._rebuild_geometry()

            # --- Handle Input ---
            try:
                key = self.stdscr.getch()
            except curses.error: # Handle case where screen is too small
                key = -1

            if key != -1:
                # getch() can return values > 255 for special keys (KEY_RESIZE,
                # arrow keys, etc.); chr() on those is fine but only ASCII keys
                # carry meaning here. Guard so unrelated keys don't take a path
                # that assumes ASCII.
                key_char = chr(key).lower() if 0 <= key < 256 else ''
                if key_char == 'q':
                    break # Quit
                elif key_char == 'p':
                    self.paused = not self.paused
                elif key_char in ('h', '?'):
                    self._show_help()
                elif key_char == 'r':
                    self.remove_all_entities()
                    if not self._too_small():
                        self._populate()
                # KEY_RESIZE is still handled here in case it does fire
                # — but the per-frame poll above is the real workhorse.
                elif key == curses.KEY_RESIZE:
                     if self.update_term_size():
                          if self._too_small():
                              self.remove_all_entities()
                          elif not self.entities:
                              self._populate()
                          else:
                              self._rebuild_geometry()

            # --- Update and Draw ---
            if self._too_small():
                self._show_too_small()
            else:
                if not self.paused:
                     self.animate()
                if not self.paused or self.needs_redraw:
                     self.draw_screen()

            # --- Frame Limiting --- (monotonic clock so wall-clock jumps
            # don't trigger huge sleep_time values or freeze the loop).
            current_time = time.monotonic()
            elapsed = current_time - last_time
            sleep_time = frame_delay - elapsed
            if sleep_time > 0:
                time.sleep(sleep_time)
            last_time = time.monotonic()

# --- Environment Creation ---
def create_environment(anim):
    water_line_segment_shapes = WATER_LINE_SEGMENTS
    segment_size = len(water_line_segment_shapes[0])
    # Use integer division //
    segment_repeat = anim.width // segment_size + 2 # Ensure full coverage

    for i, base_seg in enumerate(water_line_segment_shapes):
        full_seg = (base_seg * segment_repeat)[:anim.width] # Tile and trim
        depth_key = f'water_line{i}'
        entity = Entity(
            name=f"water_seg_{i}",
            type="waterline",
            shape=full_seg,
            pos=(0, i + 5, DEPTH[depth_key]), # Y position increases downwards
            default_color_char='c', # Cyan
            physical=True, # Bubbles collide with this
        )
        anim.add_entity(entity)

def create_castle(anim):
    castle_image = CASTLE_SHAPE
    castle_mask = CASTLE_MASK
    castle_height = castle_image.count('\n')
    castle_width = max(len(line) for line in castle_image.split('\n'))

    castle_x = max(0, anim.width - castle_width - 1) # Place near right edge
    castle_y = max(0, anim.height - castle_height - 1) # Place near bottom

    entity = Entity(
        name="castle",
        shape=castle_image,
        color_map=castle_mask, # Use the mask directly
        pos=(castle_x, castle_y, DEPTH['castle']),
        default_color_char='y', # Default Yellow for parts not in mask
    )
    anim.add_entity(entity)

# --- Seaweed ---
def create_all_seaweed(anim):
    # Use integer division //
    seaweed_count = max(1, anim.width // 15)
    for _ in range(seaweed_count):
        create_seaweed(None, anim) # Pass None for old_seaweed initially

def create_seaweed(old_seaweed, anim):
    # This function now acts as both the initial creator and the death callback
    height = random.randint(3, 6)
    seaweed_frames = ['', ''] # Two frames for animation
    for i in range(height):
        left_side = i % 2
        right_side = 1 - left_side
        seaweed_frames[left_side] += " (\n"
        seaweed_frames[right_side] += ")\n"

    # Trim trailing newline
    seaweed_frames = [frame.rstrip() for frame in seaweed_frames]

    seaweed_height = height
    seaweed_width = 2

    x = random.randint(1, max(1, anim.width - seaweed_width - 1))
    y = max(0, anim.height - seaweed_height -1) # Anchor to bottom
    anim_speed = random.uniform(0.25, 0.30) # Time between frames

    # Seaweed lives for 8 to 12 minutes (480 to 720 seconds)
    die_time = time.time() + random.randint(480, 720)

    entity = Entity(
        name='seaweed_' + str(random.randint(100,999)),
        type='seaweed',
        shape=seaweed_frames, # Animated shape
        pos=(x, y, DEPTH['seaweed']),
        anim_speed=anim_speed,
        die_time=die_time,
        death_cb=create_seaweed, # Respawn when dead
        default_color_char='g', # Green
    )
    anim.add_entity(entity)

# --- Bubbles ---
def create_bubble(fish, anim):
    fish_w, fish_h = fish.width(), fish.height()
    fish_x, fish_y, fish_z = fish.position()
    fish_vx = fish.vx # Get fish's horizontal speed

    bubble_pos_x = fish_x + fish_w if fish_vx > 0 else fish_x -1 # Bubble starts ahead of moving fish
    bubble_pos_y = fish_y + fish_h // 2
    bubble_pos_z = fish_z - 1 # Bubble on top

    # Match the Perl original: 5 frames where the big O lingers, full
    # upward velocity of 1 cell per tick, and animation interval of 0.1s.
    bubble_shapes = ['.', 'o', 'O', 'O', 'O']

    entity = Entity(
        shape=bubble_shapes,
        type='bubble',
        pos=(bubble_pos_x, bubble_pos_y, bubble_pos_z),
        velocity=(0, -1, 0),
        anim_speed=0.1,
        die_offscreen=True,
        physical=True, # Collidable
        coll_handler=bubble_collision,
        default_color_char='C', # Bright Cyan
        die_frame=15, # Die after animating a few times if not popped
    )
    anim.add_entity(entity)

def bubble_collision(bubble, anim):
    """ Bubble collision handler. """
    for col_obj in bubble.collisions:
        if col_obj.type == 'waterline':
            bubble.kill()
            # Add a small 'pop' effect? (Optional)
            # create_splat(anim, *bubble.position(), splat_char='.')
            break # No need to check further

# --- Fish ---
def create_all_fish(anim):
    # Adjust fish count based on screen area below waterline
    water_line_y = 9 # Approximate top of water
    underwater_height = max(1, anim.height - water_line_y)
    screen_area = underwater_height * anim.width
    # Use integer division //
    fish_count = max(1, screen_area // 350)

    for _ in range(fish_count):
        create_fish(None, anim) # Pass None for old_fish initially

def create_fish(old_fish, anim):
    """ Chooses between old and new fish styles based on global flag. """
    if NEW_FISH:
        if random.randint(0, 11) > 8:
            create_new_fish_entity(anim)
        else:
            create_old_fish_entity(anim)
    else:
        create_old_fish_entity(anim)

# (Keep add_new_fish_data, add_old_fish_data, add_fish_entity functions separate for clarity)
def get_new_fish_data():
    return NEW_FISH_DATA

def get_old_fish_data():
    return OLD_FISH_DATA

def rand_color_mask(color_mask_template, palette=None):
    """ Replaces digits 1-9 in a mask template with random color chars.

    `palette` defaults to the original 12-color set; pass anim.fish_palette
    to draw from the extended 256-color set when available.
    """
    if not color_mask_template:
        return None
    colors = palette if palette else BASE_FISH_PALETTE
    mask = color_mask_template
    # Replace numbers (except 4 which is White) with random colors
    for i in range(1, 10):
        if i == 4: continue # Skip 4 (eye color - white)
        color = random.choice(colors)
        mask = mask.replace(str(i), color)
    # Replace 4 with W (White)
    mask = mask.replace('4', 'W')
    return mask


def create_fish_entity(anim, fish_data):
    """ Creates a single fish entity from the provided data list. """
    fish_num = random.randrange(len(fish_data))
    shape_l, mask_l, shape_r, mask_r = fish_data[fish_num]

    # Randomly choose direction
    moving_right = random.choice([True, False])

    # Select shape and mask based on direction
    shape = shape_l if moving_right else shape_r  # shape_l is right-facing, shape_r is left-facing
    mask_template = mask_l if moving_right else mask_r

    # Calmer aquarium feel — Perl's [0.25, 2.25] makes fish whiz past too
    # fast at the dt-scaled tick rate, so cap at 1.25.
    speed = random.uniform(0.25, 1.25)
    vx = speed if moving_right else -speed  # Positive for right, negative for left
    vy = 0  # Fish move horizontally

    # Z depth between fish_start and fish_end. Use a continuous float so
    # two fish (which would otherwise tie at one of 18 integer buckets on
    # a populated tank) sort deterministically — fixes the "z-masking"
    # flicker where overlapping fish swap front/back unpredictably.
    z = random.uniform(DEPTH['fish_start'], DEPTH['fish_end'] + 0.999)

    # Create the actual color map from the template
    color_map = rand_color_mask(mask_template, palette=anim.fish_palette)

    # Calculate initial position
    temp_entity = Entity(shape=shape)  # Temp to get dimensions
    fish_height = temp_entity.height()
    fish_width = temp_entity.width()

    # Vertical position constraints
    min_y = 9  # Below waterline
    max_y = max(min_y, anim.height - fish_height - 1)
    y = random.randint(min_y, max_y)

    # Horizontal position: offscreen left for right-moving, right edge for left-moving
    x = -fish_width if moving_right else anim.width - 1

    entity = Entity(
        type='fish',
        shape=shape,
        auto_trans=True,
        color_map=color_map,
        pos=(x, y, z),
        velocity=(vx, vy, 0),
        update_cb=fish_update,  # Custom logic like bubbles
        die_offscreen=True,
        death_cb=create_fish,  # Respawn a new fish when this one dies
        physical=True,
        coll_handler=fish_collision,
        default_color_char='y',  # Default Yellow if mask is incomplete
    )
    anim.add_entity(entity)

def create_new_fish_entity(anim):
     create_fish_entity(anim, get_new_fish_data())

def create_old_fish_entity(anim):
     create_fish_entity(anim, get_old_fish_data())

# --- Fish Callbacks ---
def fish_update(fish, anim):
    """ Custom update logic for fish (e.g., creating bubbles). """
    # Add a bubble occasionally
    if random.randint(0, 100) > 97:
        create_bubble(fish, anim)

def fish_collision(fish, anim):
    """ Fish collision handler. """
    for col_obj in fish.collisions:
         # Only check collision with 'teeth' type (from shark)
        if col_obj.type == 'teeth':
            # Smaller fish get eaten
            if fish.height() <= 5:
                 create_splat(anim, *fish.position()) # Create blood splat
                 fish.kill()
                 break # Fish is dead, stop checking

# --- Splat Effect ---
def create_splat(anim, x, y, z, splat_char='*'):
    if splat_char == '*':
        splat_shapes = SPLAT_SHAPES
    else:
        splat_shapes = [s.replace('*', splat_char) for s in SPLAT_SHAPES]

    splat_x = x - 4 # Center the splat approx where the fish was
    splat_y = y - 2
    splat_z = z - 2 # Slightly in front of original fish

    entity = Entity(
        shape=splat_shapes,
        pos=(splat_x, splat_y, splat_z),
        default_color_char='R', # Bright Red
        anim_speed=0.25, # How fast the splat animates
        transparent_char=' ',
        die_frame=15, # Match Perl: die after ~15 anim ticks (cycles through frames a few times)
    )
    anim.add_entity(entity)

# --- Shark ---
def create_shark(old_ent, anim):
    shark_image = SHARK_SHAPES
    shark_mask = SHARK_MASKS

    dir = random.randrange(2) # 0 = left, 1 = right
    shark_shape = shark_image[dir]
    shark_mask_str = shark_mask[dir]
    shark_height = shark_shape.count('\n')
    shark_width = max(len(line) for line in shark_shape.split('\n'))

    speed = 2.0
    vx = speed if dir == 0 else -speed
    vy = 0

    # Y position constraints (allow space for shape)
    min_y = 9 # Below waterline
    max_y = max(min_y, anim.height - shark_height - 1)
    y = random.randint(min_y, max_y)

    # X position (start offscreen)
    x = -shark_width if dir == 0 else anim.width

    # Teeth column lands inside the mouth cluster of the *Python* shark
    # art (`.((` / `(|/|/|/|/` for dir=0 around col 47-49; `\|\|\|\|`
    # for dir=1 around col 4-12). Y offset is the row holding the teeth
    # glyphs in both shapes.
    teeth_offset_x = 48 if dir == 0 else 8
    teeth_offset_y = 7
    teeth_x = x + teeth_offset_x
    teeth_y = y + teeth_offset_y

    # Create teeth entity (invisible, used for collision). Note: do NOT
    # set die_offscreen=True here. The teeth is a 1-char entity but
    # starts offscreen with the shark (which is ~60 chars wide and only
    # partially onscreen). die_offscreen would kill the teeth before its
    # first move, so the shark would never bite anything. Death is
    # driven by the shark's death callback instead.
    teeth = Entity(
        type='teeth',
        shape="*",
        pos=(teeth_x, teeth_y, DEPTH['shark'] + 1),
        velocity=(vx, vy, 0),
        physical=True,
    )
    anim.add_entity(teeth)

    # Create shark entity
    shark = Entity(
        type="shark",
        shape=shark_shape,
        color_map=shark_mask_str,
        auto_trans=True,
        pos=(x, y, DEPTH['shark']),
        default_color_char='W', # Match Perl: bright white default
        velocity=(vx, vy, 0),
        die_offscreen=True,
        death_cb=shark_death, # Custom death handler
        death_cb_args=[teeth], # Pass teeth entity to death callback
    )
    anim.add_entity(shark)


def shark_death(shark, anim, teeth_entity):
    """ Shark death callback: kill the associated teeth entity and spawn a new random object. """
    if teeth_entity:
         teeth_entity.kill()
    # Spawn a new random object to replace the shark
    create_random_object(shark, anim)


# --- Ship ---
def create_ship(old_ent, anim):
    ship_image = SHIP_SHAPES
    ship_mask = SHIP_MASKS

    dir = random.randrange(2) # 0 = left, 1 = right
    shape = ship_image[dir]
    mask = ship_mask[dir]
    ship_height = shape.count('\n')
    ship_width = max(len(line) for line in shape.split('\n'))

    speed = 1.0
    vx = speed if dir == 0 else -speed
    vy = 0
    y = 0 # At the top of the screen

    # X position (start offscreen)
    x = -ship_width if dir == 0 else anim.width

    entity = Entity(
        type="ship",
        shape=shape,
        color_map=mask,
        auto_trans=True,
        pos=(x, y, DEPTH['water_gap1']), # Z-depth for waterline effect
        default_color_char='Y', # Yellow default
        velocity=(vx, vy, 0),
        die_offscreen=True,
        death_cb=create_random_object, # Spawn next random object
    )
    anim.add_entity(entity)

# --- Whale ---
def create_whale(old_ent, anim):
    whale_image = WHALE_SHAPES
    whale_mask = WHALE_MASKS
    water_spout_frames = WATER_SPOUT_FRAMES

    dir = random.randrange(2) # 0 = left, 1 = right
    base_whale_shape = whale_image[dir]
    base_whale_mask = whale_mask[dir]
    whale_height = base_whale_shape.count('\n')
    whale_width = max(len(line) for line in base_whale_shape.split('\n'))

    speed = 1.0
    vx = speed if dir == 0 else -speed
    vy = 0
    y = 0 # Top of screen

    # X position (start offscreen)
    x = -whale_width - 5 if dir == 0 else anim.width + 5 # Add margin

    # Spout alignment needs careful adjustment based on whale shape
    spout_align_x = 11 if dir == 0 else 1 # Column offset for spout start

    whale_anim_shapes = []
    whale_anim_masks = []

    # Match the Perl original: 5 silent frames (no spout) followed by
    # the 7 spout-animation frames, so the whale swims a few seconds
    # between exhalations.
    silent_prefix = "\n\n\n" + base_whale_shape.strip('\n')
    for _ in range(5):
        whale_anim_shapes.append(silent_prefix)
        whale_anim_masks.append(base_whale_mask)

    # Then the actual water-spout cycle.
    for spout_frame in water_spout_frames:
         aligned_spout_lines = []
         for line in spout_frame.split('\n'):
             aligned_spout_lines.append(" " * spout_align_x + line)
         aligned_spout = "\n".join(aligned_spout_lines)
         combined_shape = aligned_spout.rstrip('\n') + "\n" + base_whale_shape.strip('\n')
         combined_mask = ("\n" * spout_frame.count('\n')) + base_whale_mask
         whale_anim_shapes.append(combined_shape)
         whale_anim_masks.append(combined_mask)


    entity = Entity(
        type="whale",
        shape=whale_anim_shapes, # Animated shape list
        color_map=whale_anim_masks, # Animated mask list (basic)
        auto_trans=True,
        pos=(x, y, DEPTH['water_gap2']),
        default_color_char='B', # Blue default
        velocity=(vx, vy, 0, 1.0), # 4th arg = animation speed modifier (1.0 normal)
        anim_speed=0.8, # Time between animation frames (whale/spout cycle)
        die_offscreen=True,
        death_cb=create_random_object,
    )
    anim.add_entity(entity)


# --- Sea Monster ---
def create_monster(old_ent, anim):
    if NEW_MONSTER:
         create_new_monster_entity(anim)
    else:
         create_old_monster_entity(anim)

def get_new_monster_data():
    return NEW_MONSTER_FRAMES, NEW_MONSTER_MASKS

def get_old_monster_data():
    return OLD_MONSTER_FRAMES, OLD_MONSTER_MASKS

def create_monster_entity(anim, monster_data, monster_mask_data):
    """ Creates a sea monster entity. """
    dir = random.randrange(2) # 0 = left, 1 = right
    shapes = monster_data[dir]
    mask_base = monster_mask_data[dir]
    num_frames = len(shapes)

    # Use the same mask for all frames of a given direction
    masks = [mask_base] * num_frames

    # Calculate dimensions from the first frame
    temp_entity = Entity(shape=shapes[0])
    mon_height = temp_entity.height()
    mon_width = temp_entity.width()

    speed = 2.0
    vx = speed if dir == 0 else -speed
    vy = 0
    y = 2 # Fixed Y position near the top

    # X position (start offscreen)
    x = -mon_width if dir == 0 else anim.width

    entity = Entity(
        type="monster",
        shape=shapes, # Animated shape list
        color_map=masks, # Basic mask list
        auto_trans=True,
        pos=(x, y, DEPTH['water_gap2']), # Z-depth near whale
        default_color_char='G', # Green default
        velocity=(vx, vy, 0, 0.25), # 4th arg = animation speed modifier
        anim_speed=1.0, # Base time between frames (modified by velocity[3])
        die_offscreen=True,
        death_cb=create_random_object,
    )
    anim.add_entity(entity)

def create_new_monster_entity(anim):
    data, masks = get_new_monster_data()
    create_monster_entity(anim, data, masks)

def create_old_monster_entity(anim):
    data, masks = get_old_monster_data()
    create_monster_entity(anim, data, masks)

# --- Big Fish ---
def create_big_fish(old_ent, anim):
    """ Chooser for different big fish types. """
    if NEW_FISH:
        if random.randint(0, 2) > 0: # 2/3 chance for type 2
             create_big_fish_2(old_ent, anim)
        else:
             create_big_fish_1(old_ent, anim)
    else:
        create_big_fish_1(old_ent, anim)


def create_big_fish_1(old_ent, anim):
    big_fish_image = BIG_FISH_1_SHAPES
    big_fish_mask = BIG_FISH_1_MASKS

    dir = random.randrange(2) # 0 = left, 1 = right
    shape = big_fish_image[dir]
    mask_template = big_fish_mask[dir] # Mask uses '1' and '2'
    fish_height = shape.count('\n')
    fish_width = max(len(line) for line in shape.split('\n'))

    speed = 3.0
    vx = speed if dir == 0 else -speed
    vy = 0

    # Y position constraints
    min_y = 9
    max_y = max(min_y, anim.height - fish_height - 1)
    y = random.randint(min_y, max_y)

    # X position (start offscreen)
    x = -fish_width if dir == 0 else anim.width

    # Apply random colors to '1' and '2' in the mask
    # Let '1' be the main body color, '2' be the highlight
    colors = anim.fish_palette
    body_color = random.choice(colors)
    highlight_color = random.choice([c for c in colors if c != body_color]) # Different highlight
    color_map = mask_template.replace('1', body_color).replace('2', highlight_color)
    # 'W' for eye remains white

    entity = Entity(
        type="big_fish",
        shape=shape,
        color_map=color_map,
        auto_trans=True,
        pos=(x, y, DEPTH['shark']), # Same depth as shark
        default_color_char='Y', # Fallback color
        velocity=(vx, vy, 0),
        die_offscreen=True,
        death_cb=create_random_object,
    )
    anim.add_entity(entity)


def create_big_fish_2(old_ent, anim):
    big_fish_image = BIG_FISH_2_SHAPES
    big_fish_mask = BIG_FISH_2_MASKS

    dir = random.randrange(2) # 0 = left, 1 = right
    shape = big_fish_image[dir]
    mask_template = big_fish_mask[dir] # Mask uses '1' and '2'
    fish_height = shape.count('\n')
    fish_width = max(len(line) for line in shape.split('\n'))

    speed = 2.5
    vx = speed if dir == 0 else -speed
    vy = 0

    # Y position constraints
    min_y = 9
    max_y = max(min_y, anim.height - fish_height - 1)
    y = random.randint(min_y, max_y)

    # X position (start offscreen)
    x = -fish_width if dir == 0 else anim.width

    # Apply random colors to '1' and '2'
    colors = anim.fish_palette
    body_color = random.choice(colors)
    fin_color = random.choice([c for c in colors if c != body_color])
    color_map = mask_template.replace('1', body_color).replace('2', fin_color)
    # 'W' for eye remains white

    entity = Entity(
        type="big_fish",
        shape=shape,
        color_map=color_map,
        auto_trans=True,
        pos=(x, y, DEPTH['shark']),
        default_color_char='Y',
        velocity=(vx, vy, 0),
        die_offscreen=True,
        death_cb=create_random_object,
    )
    anim.add_entity(entity)

# --- Random Object Handling ---
RANDOM_OBJECT_POOL = [
    create_ship,
    create_whale,
    create_monster,
    create_big_fish,
    create_shark,
]

def create_random_object(dead_object, anim):
    """ Selects and creates a new random object, usually when one dies offscreen. """
    # The dead_object isn't actually used here, but matches Perl callback signature
    random_func = random.choice(RANDOM_OBJECT_POOL)
    random_func(None, anim) # Call the chosen creation function


# --- Utility Functions ---
def center_text(width, text):
    """ Centers text within a given width. """
    text_len = len(text)
    if text_len >= width:
        # Truncate if too long (simple truncation)
        return text[:width-3] + "..."
    padding = (width - text_len) // 2
    return " " * padding + text

# --- Signal Handling ---
def signal_handler(sig, frame):
    """ Cleanly exit on Ctrl+C; SIGWINCH is intentionally NOT handled
    here so ncurses' own handler stays in place. (When a Python signal
    handler is registered for SIGWINCH it shadows the ncurses one, and
    the KEY_RESIZE event no longer makes it into getch()'s queue —
    which is the proximate cause of "tmux pane resize does nothing".) """
    if sig == signal.SIGINT:
        sys.exit(0)  # atexit handler will cleanup curses


# --- Cleanup Function ---
def cleanup():
    """ Restore terminal settings.

    By the time atexit fires, curses.wrapper() has usually already called
    endwin(); calling further curses query functions like has_colors() at
    that point is undefined behavior (and segfaults on some libcurses
    builds). Just attempt restoration once and swallow errors.
    """
    try:
        curses.nocbreak()
        curses.echo()
        curses.endwin()
    except Exception:
        pass

# --- Main Execution ---
animation_instance = None # Global reference for signal handler

def parse_args(argv=None):
    parser = argparse.ArgumentParser(
        prog="asciiquarium",
        description=f"Asciiquarium v{VERSION} - ASCII Aquarium Animation",
    )
    parser.add_argument('-c', '--classic', action='store_true',
                        help="use classic (original) fish and monster graphics")
    parser.add_argument('--fps', type=float, default=20.0, metavar='N',
                        help="target frames per second (default: 20)")
    parser.add_argument('--no-color', action='store_true',
                        help="disable color; use bold/normal attributes only")
    parser.add_argument('--seed', type=int, default=None, metavar='N',
                        help="seed the random generator for reproducible runs")
    parser.add_argument('--version', action='version',
                        version=f"asciiquarium {VERSION}")
    args = parser.parse_args(argv)
    if args.fps <= 0:
        parser.error("--fps must be positive")
    return args

def main(stdscr, args):
    global animation_instance

    # --- Curses Setup ---
    stdscr.clear()
    curses.curs_set(0) # Hide cursor
    stdscr.keypad(True) # Enable keypad mode (for KEY_RESIZE etc.)
    stdscr.nodelay(True) # Make getch() non-blocking

    # --- Create and Run Animation ---
    animation_instance = Animation(
        stdscr,
        classic_mode=args.classic,
        fps=args.fps,
        use_color=not args.no_color,
    )
    animation_instance.run() # Start the main loop

    return 0


def cli_entry():
    """ Console-script entry point (referenced from pyproject.toml). """
    # Parse args before entering curses so --help / --version print cleanly.
    cli_args = parse_args()
    if cli_args.seed is not None:
        random.seed(cli_args.seed)

    # Register cleanup function to run on exit
    atexit.register(cleanup)

    # Only handle SIGINT here. SIGWINCH is left to ncurses (registering
    # a Python handler would shadow ncurses' own and break KEY_RESIZE
    # delivery, especially inside tmux panes).
    signal.signal(signal.SIGINT, signal_handler)

    exit_code = 0
    try:
        # curses.wrapper handles terminal setup/teardown
        exit_code = curses.wrapper(main, cli_args)
    except curses.error as e:
         # Cleanup might have already run via atexit, but try again if wrapper fails early
         cleanup()
         print(f"\nCurses Error: {e}", file=sys.stderr)
         print("Ensure your terminal window is large enough and supports colors.", file=sys.stderr)
         exit_code = 1
    except Exception as e:
         # Catch other unexpected errors
         cleanup() # Ensure cleanup runs even if error is outside curses
         print(f"\nAn unexpected error occurred: {e}", file=sys.stderr)
         import traceback
         traceback.print_exc()
         exit_code = 1

    sys.exit(exit_code)


if __name__ == "__main__":
    cli_entry()
