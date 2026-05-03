"""Argument parsing, signal handling, curses lifecycle, console-script
entry point."""

from __future__ import annotations

import argparse
import atexit
import curses
import random
import signal
import sys
from typing import Sequence

from animation import Animation
from constants import VERSION


# --- Signal Handling ---
def signal_handler(sig: int, frame) -> None:
    """ Cleanly exit on Ctrl+C; SIGWINCH is intentionally NOT handled
    here so ncurses' own handler stays in place. (When a Python signal
    handler is registered for SIGWINCH it shadows the ncurses one, and
    the KEY_RESIZE event no longer makes it into getch()'s queue —
    which is the proximate cause of "tmux pane resize does nothing".) """
    if sig == signal.SIGINT:
        sys.exit(0)  # atexit handler will cleanup curses



# --- Cleanup Function ---
def cleanup() -> None:
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
def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
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

def main(stdscr, args: argparse.Namespace) -> int:
    # --- Curses Setup ---
    stdscr.clear()
    curses.curs_set(0) # Hide cursor
    stdscr.keypad(True) # Enable keypad mode (for KEY_RESIZE etc.)
    stdscr.nodelay(True) # Make getch() non-blocking

    # --- Create and Run Animation ---
    Animation(
        stdscr,
        classic_mode=args.classic,
        fps=args.fps,
        use_color=not args.no_color,
    ).run()
    return 0


def cli_entry() -> None:
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

