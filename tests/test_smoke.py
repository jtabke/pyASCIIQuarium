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
        patch.object(curses, 'resizeterm', lambda *a, **k: None),
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

    def test_bubble_pops_at_waterline(self):
        """ Generic-bbox collision detection must let bubbles bump into
        the waterline and trigger their coll_handler — previously the
        check_collisions function early-returned when no shark teeth
        were on screen, so bubbles never popped. """
        import asciiquarium
        anim = asciiquarium.Animation(FakeStdscr(h=30, w=120), fps=20.0)
        asciiquarium.create_environment(anim)
        asciiquarium.create_old_fish_entity(anim)
        fish = next(e for e in anim.entities if e.type == 'fish')
        fish.x, fish.y = 50, 20
        # Spawn a bubble directly under the waterline (waterlines are
        # at y=5..8) and warp it up so the next tick overlaps.
        asciiquarium.create_bubble(fish, anim)
        bubble = next(e for e in anim.entities if e.type == 'bubble')
        bubble.y = 8  # Sitting on the lowest waterline row.
        anim.animate()
        # bubble_collision should have killed it; the entity is removed
        # in the same animate() pass.
        self.assertNotIn(bubble, anim.entities)

    def test_exterior_transparency_preserves_interior(self):
        """ When auto_trans=True, leading/trailing spaces on each line
        should be marked transparent ('?') but interior spaces should
        survive — that's how a fish silhouette occludes back-layer fish
        instead of letting characters show through. """
        import asciiquarium
        e = asciiquarium.Entity(
            type='fish',
            shape="\n  /\\\n / \\\n  \\/\n",
            auto_trans=True,
        )
        # auto_trans was consumed at construction time.
        self.assertFalse(e.auto_trans)
        # Leading spaces became '?'; the space between / and \ on row 1
        # is interior and stays a space.
        # row 0 was "  /\\" → "??/\\"
        self.assertEqual(e._lines[0], '??/\\')
        # row 1 was " / \\" → "?/ \\"  (interior single space preserved)
        self.assertEqual(e._lines[1], '?/ \\')
        # row 2 was "  \\/" → "??\\/"
        self.assertEqual(e._lines[2], '??\\/')

    def test_foreground_bbox_claim_blocks_back_fish_bleed(self):
        """ Two overlapping fish: the closer one's bounding box must
        prevent the further one from rendering anything inside that
        rectangle, including through the closer fish's transparent
        rows/cols. The castle behind both should still poke through
        the closer fish's transparent cells (background pass writes
        first). """
        import random
        random.seed(0)
        import asciiquarium as aq

        # Fake stdscr that captures every addch into a 2D grid.
        class Cap:
            def __init__(self, h=20, w=60):
                self.h, self.w = h, w
                self.grid = [[' '] * w for _ in range(h)]
            def getmaxyx(self): return (self.h, self.w)
            def getch(self): return -1
            def erase(self):
                self.grid = [[' '] * self.w for _ in range(self.h)]
            def clear(self): self.erase()
            def refresh(self): pass
            def nodelay(self, _): pass
            def keypad(self, _): pass
            def addnstr(self, *a, **k): pass
            def addstr(self, *a, **k): pass
            def addch(self, y, x, ch, attr=0):
                if 0 <= y < self.h and 0 <= x < self.w:
                    self.grid[y][x] = ch

        stdscr = Cap()
        anim = aq.Animation(stdscr, fps=20.0)
        aq.create_old_fish_entity(anim)
        aq.create_old_fish_entity(anim)
        fish_a, fish_b = [e for e in anim.entities if e.type == 'fish']
        # Front fish (lower z = closer) at (5, 10).
        fish_a.x, fish_a.y, fish_a.z = 5, 10, 5
        # Back fish overlaps front horizontally.
        fish_b.x, fish_b.y, fish_b.z = 7, 11, 12
        anim.draw_screen()

        # Inside front fish's bounding box, no character from the back
        # fish should appear. Front bbox: cols [5, 5+w), rows [10, 10+h).
        fa_x1 = int(fish_a.x)
        fa_x2 = fa_x1 + fish_a.width()
        fa_y1 = int(fish_a.y)
        fa_y2 = fa_y1 + fish_a.height()
        front_lines = fish_a._lines
        for y in range(fa_y1, fa_y2):
            row_idx = y - fa_y1
            line = front_lines[row_idx] if row_idx < len(front_lines) else ''
            for x in range(fa_x1, fa_x2):
                col_idx = x - fa_x1
                shape_char = line[col_idx] if col_idx < len(line) else ' '
                drawn = stdscr.grid[y][x]
                if shape_char in ('?', ' '):
                    # Transparent cell of the front fish: must be empty
                    # in this scene (no castle, nothing else drew here).
                    self.assertEqual(drawn, ' ',
                        f'cell ({y},{x}) should be empty but contains {drawn!r}')
                else:
                    # Opaque cell: must show the front fish's char.
                    self.assertEqual(drawn, shape_char,
                        f'cell ({y},{x}) expected {shape_char!r} got {drawn!r}')

    def test_silent_resize_in_run_loop(self):
        """ tmux panes resize without delivering KEY_RESIZE through
        getch(). The run loop must still pick up the new dimensions
        via per-frame polling. """
        import asciiquarium
        stdscr = FakeStdscr(h=30, w=120)
        anim = asciiquarium.Animation(stdscr, fps=20.0)
        anim._populate()
        # Capture the original waterline width.
        orig_waterline = next(e for e in anim.entities if e.type == 'waterline')
        orig_w = orig_waterline.width()

        # Resize the underlying screen *without* generating KEY_RESIZE.
        stdscr.h, stdscr.w = 40, 200
        # The poll inside Animation.run() is what we want to exercise;
        # call its body directly (a single iteration's worth).
        if anim.update_term_size():
            anim._rebuild_geometry()

        # Waterlines must have been rebuilt at the new width.
        new_waterline = next(e for e in anim.entities if e.type == 'waterline')
        self.assertNotEqual(new_waterline.width(), orig_w)
        self.assertGreaterEqual(new_waterline.width(), 200 - 1)

    def test_resize_rebuilds_geometry_keeps_fish(self):
        """ Resize should drop waterlines/castle/seaweed and rebuild
        them, but keep fish/sharks/etc. in place. """
        import asciiquarium
        stdscr = FakeStdscr(h=30, w=120)
        anim = asciiquarium.Animation(stdscr, fps=20.0)
        anim._populate()
        # Pin a couple of free-floating entities so we can verify
        # they survive the resize.
        kept_ids = {id(e) for e in anim.entities
                    if e.type not in {'waterline', 'seaweed'} and e.name != 'castle'}
        self.assertGreater(len(kept_ids), 0)

        # Simulate the terminal growing.
        stdscr.h, stdscr.w = 50, 200
        anim.update_term_size()
        anim._rebuild_geometry()

        # Geometry layer regenerated.
        self.assertTrue(any(e.type == 'waterline' for e in anim.entities))
        self.assertTrue(any(e.name == 'castle' for e in anim.entities))
        self.assertTrue(any(e.type == 'seaweed' for e in anim.entities))
        # The previously-pinned free-floating entities are still alive
        # (or were at least mostly preserved — culling happens for any
        # entity now offscreen, but those at the original positions on
        # a *larger* screen can't be offscreen).
        survived = {id(e) for e in anim.entities} & kept_ids
        self.assertGreater(len(survived), 0)

        for _ in range(20):
            anim.animate()
            anim.draw_screen()


if __name__ == '__main__':
    unittest.main()
