"""Color tables, z-depth labels, version, and tick-rate calibration.

Pure data — no curses calls happen here at import (the values are
references to curses constants, which exist as soon as the curses
module is imported).
"""

import curses

VERSION = "1.1 (Python)"

# Velocity values across the codebase (fish vx ~0.25-2.25, shark/monster
# 2.0, whale/ship 1.0, bubble vy=-1) are calibrated for the Perl
# original, which called animate() at 10 Hz via halfdelay(1). Scale by
# elapsed real time so Python's --fps choice doesn't change visible
# speeds.
TICK_RATE = 10.0

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

