"""Smoke tests for asciiquarium.

Drives the Animation engine against a fake stdscr without touching the
real terminal. Catches import errors, attribute-access bugs, and any
exception in the entity / draw / collision pipeline.

Run:  python -m unittest tests.test_smoke
"""

import os
import random
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


class FakeStdscr:
    """ Minimal stand-in for a curses window. All methods are no-ops
    except getmaxyx() (returns the configured size) and getch() (always
    returns -1, i.e. no input). """

    def __init__(self, h=30, w=120):
        self.h = h
        self.w = w

    def getmaxyx(self):
        return (self.h, self.w)

    def getch(self):
        return -1

    # The renderer / setup paths call these but don't depend on side-effects.
    def erase(self): pass
    def clear(self): pass
    def refresh(self): pass
    def nodelay(self, _): pass
    def keypad(self, _): pass
    def addch(self, *_args, **_kwargs): pass
    def addstr(self, *_args, **_kwargs): pass
    def addnstr(self, *_args, **_kwargs): pass
    def scrollok(self, _): pass


def _patch_curses():
    """ Stub the curses calls that require an initialized terminal. """
    import curses
    return [
        patch.object(curses, 'start_color', lambda: None),
        patch.object(curses, 'use_default_colors', lambda: None),
        patch.object(curses, 'init_pair', lambda *a, **k: None),
        patch.object(curses, 'color_pair', lambda n: n),
        patch.object(curses, 'has_colors', lambda: True),
        patch.object(curses, 'COLORS', 256, create=True),
        patch.object(curses, 'COLOR_PAIRS', 256, create=True),
    ]


class SmokeTest(unittest.TestCase):
    def setUp(self):
        random.seed(0)  # Deterministic entity choices.
        self._patches = _patch_curses()
        for p in self._patches:
            p.start()

    def tearDown(self):
        for p in self._patches:
            p.stop()

    def test_imports(self):
        import asciiquarium  # noqa: F401
        import assets       # noqa: F401

    def test_assets_well_formed(self):
        import assets
        # Every fish entry is (shape_l, mask_l, shape_r, mask_r) of strings.
        for entry in assets.NEW_FISH_DATA + assets.OLD_FISH_DATA:
            self.assertEqual(len(entry), 4)
            for s in entry:
                self.assertIsInstance(s, str)
        # Direction-paired collections all have 2 entries.
        for pair in (assets.SHARK_SHAPES, assets.SHARK_MASKS,
                     assets.SHIP_SHAPES, assets.SHIP_MASKS,
                     assets.WHALE_SHAPES, assets.WHALE_MASKS,
                     assets.NEW_MONSTER_FRAMES, assets.NEW_MONSTER_MASKS,
                     assets.OLD_MONSTER_FRAMES, assets.OLD_MONSTER_MASKS,
                     assets.BIG_FISH_1_SHAPES, assets.BIG_FISH_1_MASKS,
                     assets.BIG_FISH_2_SHAPES, assets.BIG_FISH_2_MASKS):
            self.assertEqual(len(pair), 2, repr(pair)[:40])

    def test_animation_runs_50_frames(self):
        import asciiquarium
        stdscr = FakeStdscr(h=30, w=120)
        anim = asciiquarium.Animation(stdscr, fps=20.0)
        anim._populate()
        # Sanity: populate created entities.
        self.assertGreater(len(anim.entities), 0)
        # Drive the loop by hand. No exceptions allowed.
        for _ in range(50):
            anim.animate()
            anim.draw_screen()

    def test_tiny_terminal_does_not_populate(self):
        import asciiquarium
        stdscr = FakeStdscr(h=5, w=10)
        anim = asciiquarium.Animation(stdscr, fps=20.0)
        # On a too-small terminal, the run loop would skip _populate.
        self.assertTrue(anim._too_small())
        # Showing the message must not crash.
        anim._show_too_small()

    def test_help_overlay_renders(self):
        import asciiquarium
        stdscr = FakeStdscr(h=30, w=120)
        anim = asciiquarium.Animation(stdscr, fps=20.0)
        anim._show_help()  # Blocks on getch which always returns -1; FakeStdscr.getch returns immediately.

    def test_no_color_path(self):
        """ The monochrome fallback should populate the same color_pairs
        keys with attribute values, not curses pairs. """
        import asciiquarium
        stdscr = FakeStdscr(h=30, w=120)
        anim = asciiquarium.Animation(stdscr, fps=20.0, use_color=False)
        anim._populate()
        for _ in range(20):
            anim.animate()
            anim.draw_screen()


if __name__ == '__main__':
    unittest.main()
