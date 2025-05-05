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
import math
import atexit
from collections import namedtuple

VERSION = "1.1 (Python)"
NEW_FISH = True
NEW_MONSTER = True

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
        # Optional 4th velocity element is animation speed modifier
        self.anim_speed_modifier = velocity[3] if len(velocity) > 3 else 1.0

        self.shapes = shape if isinstance(shape, list) else [shape]
        self.color_maps = color_map if isinstance(color_map, list) else [color_map] * len(self.shapes)

        # Ensure color_maps length matches shapes length
        if len(self.color_maps) < len(self.shapes):
             self.color_maps.extend([self.color_maps[-1]] * (len(self.shapes) - len(self.color_maps)))

        self.current_frame = 0
        self.anim_speed = anim_speed # Time between frames
        self.last_anim_time = time.time()

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
        self.auto_trans = auto_trans # Treat spaces as transparent?

        self.is_alive = True
        self._width = 0
        self._height = 0
        self._lines = []
        self._color_lines = []
        self._update_dimensions() # Initial calculation

        # For collision detection
        self.collisions = []

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

    def update(self, animation_instance):
        """ Update entity state (position, animation frame, life status). """
        if not self.is_alive:
            return

        now = time.time()

        # --- Life checks ---
        if self.die_time and now >= self.die_time:
            self.kill()
            return
        if self.die_frame and self._frames_shown >= self.die_frame:
             self.kill()
             return

        # --- Animation Frame ---
        if len(self.shapes) > 1 and self.anim_speed > 0:
            if now - self.last_anim_time >= (self.anim_speed / self.anim_speed_modifier):
                self.current_frame = (self.current_frame + 1) % len(self.shapes)
                self._update_dimensions()
                self.last_anim_time = now
                self._frames_shown += 1

        # --- Movement ---
        # Note: Term::Animation applies movement based on time elapsed.
        # A simpler frame-based movement is used here for less dependency on precise timing.
        # For smoother animation, use time delta: delta_time = now - self.last_update_time; self.x += self.vx * delta_time * CHARS_PER_SECOND etc.
        self.x += self.vx
        self.y += self.vy
        # self.z += self.vz # Z movement not typically used in this script

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
    def __init__(self, stdscr, classic_mode=False):
        self.stdscr = stdscr
        self.height, self.width = stdscr.getmaxyx()
        self.entities = []
        self.paused = False
        self.needs_redraw = True # Flag to force redraw after resize etc.
        self.classic_mode = classic_mode
        self._init_colors()
        self._last_term_size = (self.height, self.width)

    def _init_colors(self):
        """ Initialize curses color pairs. """
        curses.start_color()
        curses.use_default_colors() # Allow use of default terminal background

        self.color_pairs = {}
        pair_num = 1 # Start from 1, 0 is reserved for default white on black

        for char, (fg, attr) in COLOR_CHAR_MAP.items():
             # Use -1 for default background
             try:
                 curses.init_pair(pair_num, fg, -1)
                 self.color_pairs[char] = curses.color_pair(pair_num) | attr
                 pair_num += 1
             except curses.error as e:
                 # Ran out of color pairs?
                 # Consider logging this error
                 # print(f"Warning: Could not initialize color pair for '{char}'. {e}", file=sys.stderr)
                 pass
             if pair_num > curses.COLOR_PAIRS - 1:
                 break

        # Add a default pair if needed (e.g., white on default bg)
        if 'default' not in self.color_pairs:
             try:
                  curses.init_pair(pair_num, curses.COLOR_WHITE, -1)
                  self.color_pairs['default'] = curses.color_pair(pair_num) | curses.A_NORMAL
             except curses.error:
                  self.color_pairs['default'] = curses.color_pair(0) # Fallback


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

        # Update entities
        for entity in self.entities:
            entity.update(self)

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
                             # Skip transparent characters
                             if char == entity.transparent_char or (entity.auto_trans and char == ' '):
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


    def run(self):
        """ Main animation loop. """
        global NEW_FISH, NEW_MONSTER # Allow modification based on classic mode

        # Set classic mode flags if specified
        if self.classic_mode:
            NEW_FISH = False
            NEW_MONSTER = False

        # Initial setup
        create_environment(self)
        create_castle(self)
        create_all_seaweed(self)
        create_all_fish(self)
        # Add one initial random "special" object
        RANDOM_OBJECT_POOL[random.randrange(len(RANDOM_OBJECT_POOL))](None, self)

        self.stdscr.nodelay(True) # Make getch non-blocking
        # curses.halfdelay(1) # Or use halfdelay for 0.1s timeout

        last_time = time.time()
        frame_delay = 0.05 # Target ~20 FPS (adjust as needed)

        while True:
            # --- Handle Input ---
            try:
                key = self.stdscr.getch()
            except curses.error: # Handle case where screen is too small
                key = -1

            if key != -1:
                key_char = chr(key).lower()
                if key_char == 'q':
                    break # Quit
                elif key_char == 'p':
                    self.paused = not self.paused
                elif key_char == 'r':
                    # Redraw/Restart Logic
                    self.remove_all_entities()
                    create_environment(self)
                    create_castle(self)
                    create_all_seaweed(self)
                    create_all_fish(self)
                    RANDOM_OBJECT_POOL[random.randrange(len(RANDOM_OBJECT_POOL))](None, self)
                    self.paused = False
                    self.needs_redraw = True
                # Handle resize implicitly via SIGWINCH or check here
                elif key == curses.KEY_RESIZE:
                     if self.update_term_size():
                          # Term size changed, force redraw of static elements?
                          # Current loop structure handles this by default on 'r'
                          # For dynamic resize without 'r', need to recreate/resize elements
                          self.remove_all_entities() # Simple approach: restart like 'r'
                          create_environment(self)
                          create_castle(self)
                          create_all_seaweed(self)
                          create_all_fish(self)
                          RANDOM_OBJECT_POOL[random.randrange(len(RANDOM_OBJECT_POOL))](None, self)
                          self.paused = False


            # --- Update and Draw ---
            if not self.paused:
                 self.animate()

            # Only draw if needed or not paused (to see paused state)
            # Or always draw if self.needs_redraw is True
            if not self.paused or self.needs_redraw:
                 self.draw_screen()

            # --- Frame Limiting ---
            current_time = time.time()
            elapsed = current_time - last_time
            sleep_time = frame_delay - elapsed
            if sleep_time > 0:
                time.sleep(sleep_time)
            last_time = time.time() # Use current_time or time.time()? Using current is closer to target rate

# --- Environment Creation ---
def create_environment(anim):
    water_line_segment_shapes = [
        "~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~",
        "^^^^ ^^^  ^^^   ^^^     ^^^^     ",
        "^^^^      ^^^^     ^^^     ^^     ",
        "^^      ^^^^       ^^^     ^^^^^^ "
    ]
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
    castle_image = r"""
                T~~
                |
               /^\
              /  \
 _   _   _  /    \  _   _   _
[ ]_[ ]_[ ]/ _  _ \[ ]_[ ]_[ ]
|_=__-_ =_|_[ ]_[ ]_|_=-___-__|
 | _- =  | =_ = _    |= _=   |
 |= -[]  |- = _ =    |_-=_[] |
 | =_    |= - ___    | =_ =  |
 |=  []- |-  /| |\   |=_ =[] |
 |- =_   | =| | | |  |- = -  |
 |_______|__|_|_|_|__|_______|
"""
    # Simplified mask using direct color chars from COLOR_CHAR_MAP
    castle_mask = r"""
                RR
                R
               YYY
              Y  Y
 Y   Y   Y  Y    Y  Y   Y   Y
[W]_[W]_[W]Y W  W Y[W]_[W]_[W]
|W=__-_=W|_|W|_[W]|_|W=-___-W|
 |W_-W= W|W=WW_=W W |W=W_= W |
 |W=-[W]W|W-=W_W=W W |W_-=_[W]|
 |W=_W W |W=-W___W W |W=_W= W |
 |W= W[]-|W- W/|W|\W W|=_W=[]W|
 |W-=W_W W|W=|W|W|W|W |W-=W-W |
 |WWWWWWW|WW|W|W|W|WW|WWWWWWW|
""" # Note: Mask interpretation might need fine-tuning based on desired look

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

    bubble_shapes = ['.', 'o', 'O'] # Simple animation
    bubble_vel_y = -0.5 # Move upwards (adjust speed as needed)
    bubble_anim_speed = 0.15 # How fast bubble shape changes

    entity = Entity(
        shape=bubble_shapes,
        type='bubble',
        pos=(bubble_pos_x, bubble_pos_y, bubble_pos_z),
        velocity=(0, bubble_vel_y, 0, 0.5), # Y velocity, slightly slower animation
        anim_speed=bubble_anim_speed,
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
    # Each element is (shape_left, mask_left, shape_right, mask_right)
    # Masks use number chars 1-7, 4=White(W)
    # 1: body, 2: dorsal, 3: flippers, 4: eye(W), 5: mouth, 6: tail, 7: gills
    data = [
        (r"""
  \\
 / \\
>=_('>
 \_/
  /
""", r"""
  2
 1 1
663745
 111
  3
""", r"""
  /
 / \\
<')_=<
 \_/
  \\
""", r"""
  3
 111
547366
 1 1
  2
"""),
        (r"""
    ,
    \}\
\\ .'  `\\
\}\}<  ( 6>
/  `, .'
    \}/
    '
""", r"""
    2
    22
6  11  11
661  7 45
6  11  11
    33
    3
""", r"""
   ,
  /\{
 /'  `.  /
<6 )  >\{\{
 `.  ,'  \\
   \\\{
    `
""", r"""
   3
  33
6  11  11
54 7  166
6  11  11
  22
   2
"""),
        (r"""
         \\'`.
          )  \\
(`.??????_.-`' ' '`-.
 \\ `.??.`      (o) \\_
  >  ><    (((      (
 / .`??`._    /_|  /'
(.`???????`-. _  _.-`
             /__/'

""", r"""
         1111
          1  1
111      11111 1 1111
 1 11  11       141 11
  1  11    777      5
 1 11  111     333  11
111       111 1  1111
             11111

""", r"""
      .'`/
     /  (
 .-'` ` `'-._??????.')
_/ (o)      '.??.' /
)      )))    ><  <
`\\  |_\\     _.'??'. \\
  '-._  _ .-'???????'.)
     `\\__\\
""", r"""
      1111
     1  1
  1111 1 11111      111
11 141       11  11 1
5      777     11  1
11  333     111  11 1
  1111  1 111       111
     11111
"""),
        (r"""
      ,--,_
__   _\\.---'-.
\\ '.-"    // o\\
/_.'-._   \\\\  /
      `"--(/"`
""", r"""
      22222
66   121111211
6 6111    77 41
6661111   77  1
      11113311
""", r"""
   _,--,
 .-'---./_   __
/o \\    "-.' /
\\ //   _.-'._\\
 `"\\)--"`
""", r"""
   22222
 112111121   66
14 77    1116 6
1  77   1111666
 11331111
"""),
    ]
    return data

def get_old_fish_data():
    data = [
        (r"""
      \
    ...\..,
\  /'      \
 >=    (  ' >
/  \     / /
   `"'"'/''
""", r"""
      2
    1112111
6  11      1
 66    7  4 5
6  1     3 1
   11111311
""", r"""
     /
 ,../...
/      '\  /
< '  )    =<
 \ \     /  \
  `'\'"'"'
""", r"""
     2
 1112111
1      11  6
5 4  7    66
 1 3     1  6
  11311111
"""),
        (r"""
  \
\ /--\
>=  (o>
/ \__/
   /
""",r"""
  2
6 1111
66  745
6 1111
   3
""", r"""
 /
/--\ /
<o)  =<
 \__/ \
  \
""", r"""
  2
 1111 6
547  66
 1111 6
  3
"""),
        (r"""
      \:.
\;,  ,;\\\\\,,
  \\\\\;;:::::::o
  ///;;::::::::<
 /;` ``/////``
""", r"""
      222
666  1122211
  6661111111114
  66611111111115
 666 113333311
""", r"""
     .:/
  ,,///;,  ,;/
 o:::::::;;///
>::::::::;;\\\\\
  ''\\\\\\\\\'' ';\
""", r"""
     222
  1122211  666
 4111111111666
51111111111666
  113333311 666
"""),
        (r"""
 __
><_'>
   '
""", r"""
 11
61145
   3
""", r"""
 __
<'_><
 `
""", r"""
 11
54116
 3
"""),
        (r"""
  ..\,
>='  (' >
  '''/''
""", r"""
  1121
661  745
  111311
""", r"""
 ,/..
<')  `=<
 ``\```
""", r"""
 1211
547  166
 113111
"""),
        (r"""
  \
 / \
>=_('>
 \_/
  /
""", r"""
  2
 1 1
661745
 111
  3
""", r"""
 /
/ \
<')_=<
 \_/
  \
""", r"""
  2
 1 1
547166
 111
  3
"""),
        (r"""
 ,\
>=('>
 '/
""", r"""
 12
66745
 13
""", r"""
 /
<')=<
 \`
""", r"""
 21
54766
 31
"""),
        (r"""
 __
\/ o\
/\__/
""", r"""
 11
61 41
61111
""", r"""
 __
/o \/
\__/\
""", r"""
 11
14 16
11116
"""),
    ]
    return data

def rand_color_mask(color_mask_template):
    """ Replaces digits 1-9 in a mask template with random color chars. """
    if not color_mask_template:
        return None
    colors = ['c','C','r','R','y','Y','b','B','g','G','m','M']
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

    speed = random.uniform(0.25, 1.25)
    vx = speed if moving_right else -speed  # Positive for right, negative for left
    vy = 0  # Fish move horizontally

    # Z depth between fish_start and fish_end
    z = random.randint(DEPTH['fish_start'], DEPTH['fish_end'])

    # Create the actual color map from the template
    color_map = rand_color_mask(mask_template)

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
    splat_shapes = [
        # Frames shrink over time
        f"""

   {splat_char}
  {splat_char}{splat_char}{splat_char}
   '

""", f"""

  "{splat_char};`
 "{splat_char},{splat_char}{splat_char}
 {splat_char}"'~'

""", f"""
  , ,
 " ","'
 {splat_char}" {splat_char}'"
  " ; .

""", f"""
{splat_char} ' , ' `
' ` {splat_char} . '
 ' `' ",{splat_char}
{splat_char} ' " {splat_char} .
" {splat_char} ', '
""", " " # Disappear
    ]

    splat_x = x - 4 # Center the splat approx where the fish was
    splat_y = y - 2
    splat_z = z - 2 # Slightly in front of original fish

    entity = Entity(
        shape=splat_shapes,
        pos=(splat_x, splat_y, splat_z),
        default_color_char='R', # Bright Red
        anim_speed=0.25, # How fast the splat animates
        transparent_char=' ',
        die_frame=len(splat_shapes), # Die after playing all frames
    )
    anim.add_entity(entity)

# --- Shark ---
def create_shark(old_ent, anim):
    shark_image = [
        r"""
                             __
                           ( `\
 ,??????????????????????????)   `\
;' `.????????????????????????(     `\__
 ;   `.?????????????__..---''         `~~~~-._
  `.   `.____...--''                         (b `--._
    >                                _.-'     .((     ._    )
  .`.-`--...__             .-'    -.___.....-(|/|/|/|/'
 ;.'?????????`. ...----`.___.',,,_______......---'
 '???????????'-'
""", r"""
                          __
                         /' )
                       /'   (??????????????????????????,
                 __/'     )????????????????????????.' `;
       _.-~~~~'          ``---..__?????????????.'   ;
   _.--'  b)                   ``--...____.'   .'
 (     _.     )).      `-._                    <
  `\|\|\|\|)-.....___.-    `-.         __...--'-.'.
   `---......_______,,,`.___.'----... .'?????????`.;
                                     `-`???????????`
"""
    ]
    # Mask: c=Cyan fin R=Red mouth W=White teeth
    shark_mask = [
        r"""





                             cR
                             cWWWWWWWW


""", r"""





       Rc

  WWWWWWWWc


"""
    ]

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

    # Teeth position (relative to shark) - adjust these offsets carefully!
    teeth_offset_x = 26 if dir == 0 else 14 # Approx x-offset of mouth/teeth
    teeth_offset_y = 7 # Approx y-offset of mouth/teeth
    teeth_x = x + teeth_offset_x
    teeth_y = y + teeth_offset_y

    # Create teeth entity (invisible, used for collision)
    teeth = Entity(
        type='teeth',
        shape="*", # Doesn't matter, it's not drawn visibly
        pos=(teeth_x, teeth_y, DEPTH['shark'] + 1), # Z slightly in front
        velocity=(vx, vy, 0), # Moves with the shark
        physical=True, # Can collide
        # Make it die with the shark - link via death callback?
        # Or simpler: just die offscreen with shark
        die_offscreen=True,
    )
    anim.add_entity(teeth)

    # Create shark entity
    shark = Entity(
        type="shark",
        shape=shark_shape,
        color_map=shark_mask_str,
        auto_trans=True,
        pos=(x, y, DEPTH['shark']),
        default_color_char='C', # Default Cyan
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
    ship_image = [
        r"""
    |   |   |
   )_) )_) )_)
  )___))___))___)\
 )____)____)_____)\\\
_____|____|____|____\\\\\__
\                   /
""", r"""
       |   |   |
      (_( (_( (_(
     /(___((___((___(
   //(_____(____(____(
__///____|____|____|_____
   \                   /
"""
    ]
    # y=yellow, w=white/wave
    ship_mask = [
        r"""
    y   y   y
   y_y y_y y_y
  y___yy___yy___y\w
 y____yy____yy____y\ww
YYYYYyYYYYyYYYYyYYYYwwwwwYY
Y                   Y
""", r"""
       y   |   |
      y_y y_y y_y
     wy(___yy___yy___y
   wwy(____y(____y____y
ww///YYYYyYYYYyYYYYyYYYYY
   Y                   Y
"""
    ] # Adjust 'w' placement/color for desired wave look

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
    whale_image = [
        r"""
      .-----:
     .'      `.
,????/      (o) \
\`._/         ,__)
""", r"""
   :-----.
 .'      `.
 / (o)      \????,
(__,         \_.'/
"""
    ]
    # C=Cyan spout, B=Blue body, W=White eye
    whale_mask = [
        r"""
      CCCCCC
     C      C
BBBBBC    CWB C
BBD_B         BBBB
""", r"""
   CCCCCC
 C      C
 C BWC    CBbbbb
BBBB         BD_BB
""" # Adjusted slightly, 'D' could be dark blue if available/mapped
    ]
    water_spout_frames = [
        "\n\n\n", # Initial delay - no spout
        "\n\n\n",
        "\n\n\n",
        "\n\n\n",
        "\n\n\n",
        "\n\n : \n",
        "\n : \n : \n",
        "\n . .\n -:-\n  : \n",
        "\n . .\n.-:-.\n  : \n",
        "\n . .\n'.-:-.`\n' : '\n",
        "\n\n .- -.\n; : ;\n",
        "\n\n\n;   ;\n",
        "\n\n\n\n" # Spout disappears
    ]

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

    # Create frames combining whale and spout
    for spout_frame in water_spout_frames:
         # Prepend spout, aligning it horizontally
         aligned_spout_lines = []
         for line in spout_frame.split('\n'):
             aligned_spout_lines.append(" " * spout_align_x + line)
         aligned_spout = "\n".join(aligned_spout_lines)

         # Combine spout and whale shape (ensure newline alignment)
         # This simple concatenation might need refinement
         combined_shape = aligned_spout.rstrip('\n') + "\n" + base_whale_shape.strip('\n')

         # Pad mask to match spout height? For now, just use base mask.
         # A proper implementation would generate masks for the spout too.
         combined_mask = ("\n" * spout_frame.count('\n')) + base_whale_mask

         whale_anim_shapes.append(combined_shape)
         whale_anim_masks.append(combined_mask) # Use base mask for all frames


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
    # [ [frame1_left, frame2_left], [frame1_right, frame2_right] ]
    monster_image_pairs = [
        [
            r"""
        _???_?????????????????????_???_???????_a_a
       _{.`=`.}_??????_???_??????_{.`=`.}_????{/ ''\\_
 _????{.'  _  '.}????{.`'`.}????{.'  _  '.}??{|  ._oo)
{ \\??{/  .'?'.  \\}??{/ .-. \\}??{/  .'?'.  \\}?{/  |
""",
            r"""
                 _???_????????????????????_a_a
 _??????_???_??????_{.`=`.}_??????_???_??????{/ ''\\_
{ \\????{.`'`.}????{.'  _  '.}????{.`'`.}????{|  ._oo)
 \\ \\??{/ .-. \\}??{/  .'?'.  \\}??{/ .-. \\}???{/  |
"""
        ],
        [
            r"""
  a_a_???????_???_?????????????????????_???_
 _/'' \\}????_{.`=`.}_??????_???_??????_{.`=`.}_
(oo_.  |}??{.'  _  '.}????{.`'`.}????{.'  _  '.}????_
   |  \\}?{/  .'?'.  \\}??{/ .-. \\}??{/  .'?'.  \\}??/ }
""",
            r"""
  a_a_????????????????????_   _
 _/'' \\}??????_???_??????_{.`=`.}_??????_???_??????_
(oo_.  |}????{.`'`.}????{.'  _  '.}????{.`'`.}????/ }
   |  \\}???{/ .-. \\}??{/  .'?'.  \\}??{/ .-. \\}??/ /
"""
        ]
    ]
    # Mask: W = White eye
    monster_mask = [
        # Mask for left-moving (eyes on right)
        r"""
                                           W W



""",    # Mask for right-moving (eyes on left)
        r"""
  W W



"""
    ]
    return monster_image_pairs, monster_mask

def get_old_monster_data():
    # [ [frame1_left, frame2_left,...], [frame1_right, frame2_right,...] ]
    monster_image_frames = [
        [ # Left moving frames
            r"""
                                                     ____
          __??????????????????????????????????????????/  o  \
         /   \????????_?????????????????????_???????/    ____ >
 _??????|  __ |?????/   \????????_????????/   \????|    |
| \?????|  || |????|     |?????/   \?????|     |???|    |
""",
            r"""
                                                     ____
                                       __?????????/  o  \
           _?????????????????????_???????/   \?????/    ____ >
  _???????/   \????????_????????/   \????|  __ |???|    |
 | \?????|     |?????/   \?????|     |???|  || |???|    |
""",
            r"""
                                                     ____
                                __????????????????????/  o  \
 _??????????????????????_???????/   \????????_???????/    ____ >
| \??????????_????????/   \????|  __ |?????/   \????|    |
 \ \???????/   \?????|     |???|  || |????|     |???|    |
""",
            r"""
                                                     ____
               __???????????????????????????????/  o  \
 _??????????_???????/   \????????_??????????????????/    ____ >
 | \???????/   \????|  __ |?????/   \????????_??????|    |
  \ \?????|     |???|  || |????|     |?????/   \????|    |
"""
        ],
        [ # Right moving frames
            r"""
   ____
 /  o  \??????????????????????????????????????????__
< ____    \???????_?????????????????????_????????/   \
     |     |????/   \????????_????????/   \?????|  __ |??????_
     |     |???|     |?????/   \?????|     |????|  || |?????/ |
""",
            r"""
   ____
 /  o  \?????????__
< ____    \?????/   \???????_?????????????????????_
     |     |???|  __ |????/   \????????_????????/   \???????_
     |     |???|  || |???|     |?????/   \?????|     |?????/ |
""",
            r"""
   ____
 /  o  \????????????????????__
< ____    \???????_????????/   \???????_??????????????????????_
     |     |????/   \?????|  __ |????/   \????????_??????????/ |
     |     |???|     |????|  || |???|     |?????/   \???????/ /
""",
            r"""
   ____
 /  o  \???????????????????????????????__
< ____    \??????????????????_????????/   \???????_??????????_
     |     |??????_????????/   \?????|  __ |????/   \???????/ |
     |     |????/   \?????|     |????|  || |???|     |?????/ /
"""
        ]
    ]
    # Mask: W = White eye
    monster_mask = [
        # Mask for left-moving (eye on right)
        r"""
                                                         W



""",    # Mask for right-moving (eye on left)
        r"""
    W



"""
    ]
    return monster_image_frames, monster_mask

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
    big_fish_image = [
        r"""
 ______
`""-.  `````-----.....__
     `.  .     .       `-.
       :    .     .       `.
 ,?????:   .     .         _ :
: `.???:                (@) `._
 `. `..'     .     =`-.     .__)
  ;     .        =  ~  :   .-"
.' .'`.   .     . =.-'  `._ .'
: .'???:             .   .'
 '???.'.   .     .    .-'
  .'____....----''.'=.'
  ""?????????????.'.'
               ''"'`
""", r"""
               ______
       __.....-----'''''  .-""'
     .-'      .     .  .'
    .'       .     .    :
   : _           .    .  :?????,
 _.' (@)                 :???.' :
(__.       .-'=     .    `..' .'
 "-.    :  ~  =        .    ;
  `. _.'  `-.=  .     .   .'`. `.
     `.   .             :???`. :
      `-.   .     .    . `.???`
        `.=`.``----....____`.
         `.`.?????????????""
            '`"``
"""
    ]
    # Mask: 1=Body, 2=Highlights/Dots, W=Eye
    big_fish_mask = [
        r"""
 111111
111111 1111111111111111
     11  2     2       111
       1    2     2       11
 1111111   2     2         1 1
1 111111                1W1 111
 11 1111     2     1111     1111
  1     2        1  1  1   111
 11 1111   2     2 1111  111 11
1 111111             2   11
 1111111 2     2    2  111
  111111111111111111111
  11111111111111111111
               11111
""", r"""
               111111
       11111111111111111 111111
     111      2     2  11
    11       2     2    1
   1 1         2    2  1111111
 111 1W1                111111 1
1111     1111     2     1111 11
 111   1  1  1        2     1
 11 111  1111  2     2   1111 11
  11   2             111111 1
   111  2     2    2 1111111
    111111111111111111111
     11111111111111111111
            11111
"""
    ]

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
    colors = ['c','C','r','R','y','Y','b','B','g','G','m','M']
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
    big_fish_image = [
        r"""
              _ _ _
           .='\\ \\ \\`"=,
         .'\\ \\ \\ \\ \\ \\ \\
\\'=._?????/ \\ \\ \\_\\_\\_\\_\\_\\
\\'=._'.??/\\ \\,-"`- _ - _ - '-.
 \\`=._\\|'.\\/- _ - _ - _ - _- \\
 ;"= ._\\=./_ -_ -_ \{`"=_    @ \\
  ;"=_-_=- _ -  _ - \{"=_"-    \\
  ;_=_--_.,          \{_.='   .-/
 ;.="` / ';\\       _.    _.-`
 /_.='/ \\/ /;._ _ _\{.-;`/"`
/._=_.'???'/ / / / /\{.= /
/.=' ??????`'./_/_.=`\{_/
""", r"""
           _ _ _
       ,="`/ / /'=.
      / / / / / / /'.
     /_/_/_/_/_/ / / \\?????_.='/
   .-' - _ - _ -`"-,/ /\\??.'_.='/
  / -_ - _ - _ - _ -\\/.'|/_.=`/
 / @    _="`\} _- _- _\\.=/_. =";
/     -"_="\} - _  - _ -=_-_"=;
\\-.   '=._\}           ,._--_=_;
 `-._     ._        /;' \\ `"=.;
     `"\`;-.\}_ _ _.;\\ \\/ \\'=._\\
       \\ =.\}\\ \\ \\ \\ \\'???'._=_.\\
        \\_\}`=._\\_\\.'`???????'=.\\
"""
    ]
    # Mask: 1=Body/Scales 2=Fin details W=Eye
    big_fish_mask = [
        r"""
              1 1 1
           11111 1 11111
         1111 1 1 1 1 1 1
11111111111 1 1 1 11111111111
111111111111 1111112 2 2 2 2 111
 1111111111111112 2 2 2 2 2 2 22 1
 111 11111111112 22 22 11111    W 1
  1111111111111112 2 2  2 2 111111    1
  11111111111111111        11111   111
 11111 111 111111       11     1111
 1111111 11 111111 1 111111111
1111111111 111 1 1 1 1111 1
11111111111111111111111111
""", r"""
           1 1 1
       11111 1 1 1111
      1 1 1 1 1 1 111
     1111111111111 1 1 11111111111
   111 2 2 2 2 2111111 11 1111111111
  1 22 2 2 2 2 2 2 21111111111111
 1 W    11111 22 22 21111111 111
1     111111 2 2  2 2 21111111
111   11111           111111111
 1111     11        11111 111111
     111111111 1 11111111 1111111
       11 1111 1 1 1 111111111111
        111111111111111111111
"""
    ]

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
    colors = ['c','C','r','R','y','Y','b','B','g','G','m','M']
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
    """ Handles signals like Ctrl+C and window resize. """
    global animation_instance # Need access to the animation instance

    if sig == signal.SIGINT:
        # Cleanly exit on Ctrl+C
        sys.exit(0) # atexit handler should cleanup curses
    elif sig == signal.SIGWINCH:
        # Handle window resize
        if animation_instance:
             # Flag for the main loop to handle resize
             # Simple approach: let getch return KEY_RESIZE
             # More direct: call update_term_size here, but beware of issues
             # calling curses functions directly from signal handlers.
             # Setting a flag is safer.
             animation_instance.needs_redraw = True
             # The getch() in the main loop should return KEY_RESIZE
             pass


# --- Cleanup Function ---
def cleanup():
    """ Restore terminal settings. """
    if 'curses' in sys.modules and curses.has_colors():
        try:
            curses.nocbreak()
            curses.echo()
            curses.endwin()
            print("Asciiquarium exited cleanly.")
        except curses.error:
            # Might happen if terminal was already closed or in a weird state
            print("Curses cleanup failed, terminal might be in an odd state.", file=sys.stderr)
            pass # Ignore errors during cleanup

# --- Main Execution ---
animation_instance = None # Global reference for signal handler

def main(stdscr):
    global animation_instance

    # --- Curses Setup ---
    stdscr.clear()
    curses.curs_set(0) # Hide cursor
    stdscr.keypad(True) # Enable keypad mode (for KEY_RESIZE etc.)
    # Non-blocking input needed for animation loop
    stdscr.nodelay(True) # Make getch() non-blocking
    # curses.halfdelay(1) # Alternative: wait 0.1s for input

    # Check for color support
    if not curses.has_colors():
        print("Error: Your terminal does not support color.", file=sys.stderr)
        return 1
    if not curses.can_change_color():
         # Optional: Warn if colors might not look exactly as intended
         # print("Warning: Terminal cannot change color definitions.", file=sys.stderr)
         pass


    # --- Argument Parsing ---
    parser = argparse.ArgumentParser(description=f"Asciiquarium v{VERSION} - ASCII Aquarium Animation")
    parser.add_argument('-c', '--classic', action='store_true',
                        help="Use classic (original) fish and monster graphics")
    args = parser.parse_args()

    # --- Create and Run Animation ---
    animation_instance = Animation(stdscr, classic_mode=args.classic)
    animation_instance.run() # Start the main loop

    return 0


if __name__ == "__main__":
    # Register cleanup function to run on exit
    atexit.register(cleanup)

    # Setup signal handlers
    signal.signal(signal.SIGINT, signal_handler)
    # SIGWINCH handling can be tricky; curses often handles it by returning
    # KEY_RESIZE from getch(). Relying on that is usually safer.
    signal.signal(signal.SIGWINCH, signal_handler) # Let's try handling it


    # Initialize curses screen using wrapper
    exit_code = 0
    try:
        # curses.wrapper handles terminal setup/teardown
        exit_code = curses.wrapper(main)
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
    finally:
        # Explicitly call cleanup just in case atexit didn't fire (e.g., os._exit)
        # Although atexit should normally cover SIGINT and normal exit.
        # cleanup() # Probably redundant with atexit
        pass

    sys.exit(exit_code)
