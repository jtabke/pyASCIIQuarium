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

    def test_bubble_pops_at_visible_waterline_cell(self):
        """ Shape-aware collision still lets bubbles pop at the waterline,
        but now the waterline's transparent spaces are not physical. """
        import asciiquarium
        anim = asciiquarium.Animation(FakeStdscr(h=30, w=120), fps=20.0)
        asciiquarium.create_environment(anim)
        asciiquarium.create_old_fish_entity(anim)
        fish = next(e for e in anim.entities if e.type == 'fish')
        fish.x, fish.y = 50, 20
        asciiquarium.create_bubble(fish, anim)
        bubble = next(e for e in anim.entities if e.type == 'bubble')
        waterline = next(e for e in anim.entities if e.type == 'waterline' and int(e.y) == 8)
        visible_x = next(i for i, ch in enumerate(waterline._lines[0]) if ch != ' ')
        bubble.x = visible_x
        bubble.y = waterline.y
        bubble.vy = 0
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

    def test_auto_trans_flood_fill_is_opt_in(self):
        """ Default auto_trans is row-based for classic open ASCII fish;
        true flood-fill remains available for closed-shape experiments. """
        import asciiquarium
        row = asciiquarium.Entity(shape="X X", auto_trans=True)
        self.assertEqual(row._lines[0], 'X X')

        flood = asciiquarium.Entity(
            shape="X X",
            auto_trans=True,
            auto_trans_mode='flood',
        )
        self.assertEqual(flood._lines[0], 'X?X')

    def test_sprite_frame_masks_and_overlap(self):
        """ SpriteFrame exposes visible/silhouette masks directly. """
        from sprite import MaskMode, SpriteFrame, masks_overlap

        frame = SpriteFrame.parse('?X ')
        self.assertFalse(frame.contains(MaskMode.VISIBLE, 0, 0))
        self.assertTrue(frame.contains(MaskMode.VISIBLE, 1, 0))
        self.assertFalse(frame.contains(MaskMode.VISIBLE, 2, 0))
        self.assertFalse(frame.contains(MaskMode.SILHOUETTE, 0, 0))
        self.assertTrue(frame.contains(MaskMode.SILHOUETTE, 1, 0))
        self.assertTrue(frame.contains(MaskMode.SILHOUETTE, 2, 0))

        probe = SpriteFrame.parse('*')
        hit, point = masks_overlap(frame, 0, 0, MaskMode.VISIBLE,
                                   probe, 0, 0, MaskMode.VISIBLE)
        self.assertFalse(hit)
        self.assertIsNone(point)
        hit, point = masks_overlap(frame, 0, 0, MaskMode.VISIBLE,
                                   probe, 1, 0, MaskMode.VISIBLE)
        self.assertTrue(hit)
        self.assertEqual(point, (1, 0))

    def test_collision_ignores_transparent_cells_after_bbox_overlap(self):
        """ AABB overlap is only the broad phase; actual collision uses
        sprite masks, so '?' cells are not physical. """
        import asciiquarium as aq
        anim = aq.Animation(FakeStdscr(h=10, w=20), fps=20.0)
        handler = lambda *_args: None
        target = aq.Entity(
            type='fish',
            shape='?X',
            pos=(5, 5, 1),
            physical=True,
            collision_mask='visible',
            coll_handler=handler,
        )
        probe = aq.Entity(
            type='teeth',
            shape='*',
            pos=(5, 5, 0),
            physical=True,
            collision_mask='visible',
        )
        anim.add_entity(target)
        anim.add_entity(probe)

        anim.check_collisions()
        self.assertEqual(target.collisions, [])

        probe.x = 6  # Now overlaps the visible X cell.
        anim.check_collisions()
        self.assertEqual(target.collisions, [probe])

    def test_collision_events_include_hit_point(self):
        """ Collision detection keeps a modern event with impact point
        alongside the legacy collisions list. """
        import asciiquarium as aq
        anim = aq.Animation(FakeStdscr(h=10, w=20), fps=20.0)
        handler = lambda *_args: None
        target = aq.Entity(
            type='fish',
            shape='?X',
            pos=(5, 5, 1),
            physical=True,
            collision_mask=aq.MaskMode.VISIBLE,
            coll_handler=handler,
        )
        probe = aq.Entity(
            type='teeth',
            shape='*',
            pos=(6, 5, 0),
            physical=True,
            collision_mask=aq.MaskMode.VISIBLE,
        )
        anim.add_entity(target)
        anim.add_entity(probe)

        anim.check_collisions()
        self.assertEqual(target.collisions, [probe])
        self.assertEqual(target.collision_events[0].other, probe)
        self.assertEqual(target.collision_events[0].point, (6, 5))

    def test_silhouette_collision_includes_interior_blanks(self):
        """ Entities can opt into silhouette masks so interior spaces are
        part of the body while exterior '?' remains transparent. """
        import asciiquarium as aq
        anim = aq.Animation(FakeStdscr(h=10, w=20), fps=20.0)
        handler = lambda *_args: None
        target = aq.Entity(
            type='fish',
            shape='X X',
            pos=(5, 5, 1),
            physical=True,
            collision_mask='silhouette',
            coll_handler=handler,
        )
        probe = aq.Entity(
            type='teeth',
            shape='*',
            pos=(6, 5, 0),
            physical=True,
            collision_mask='visible',
        )
        anim.add_entity(target)
        anim.add_entity(probe)

        anim.check_collisions()
        self.assertEqual(target.collisions, [probe])

    def test_renderer_uses_entity_default_color_when_mask_missing(self):
        """ Missing color-mask cells must keep the entity default color,
        not fall back to the terminal default pair. """
        import asciiquarium as aq

        class Cap:
            def __init__(self, h=5, w=10):
                self.h, self.w = h, w
                self.attrs = [[None] * w for _ in range(h)]
            def getmaxyx(self): return (self.h, self.w)
            def getch(self): return -1
            def erase(self):
                self.attrs = [[None] * self.w for _ in range(self.h)]
            def clear(self): self.erase()
            def refresh(self): pass
            def nodelay(self, _): pass
            def keypad(self, _): pass
            def addnstr(self, *a, **k): pass
            def addstr(self, *a, **k): pass
            def addch(self, y, x, ch, attr=0):
                if 0 <= y < self.h and 0 <= x < self.w:
                    self.attrs[y][x] = attr

        stdscr = Cap()
        anim = aq.Animation(stdscr, fps=20.0)
        entity = aq.Entity(
            shape='X',
            color_map='',
            pos=(2, 2, 1),
            default_color_char='G',
        )
        anim.add_entity(entity)
        anim.draw_screen()
        self.assertEqual(stdscr.attrs[2][2], anim.get_color_attr('G'))

    def test_shark_teeth_collision_proxy_is_red(self):
        """ The visible one-cell teeth proxy should use bright red. """
        import asciiquarium as aq
        anim = aq.Animation(FakeStdscr(h=30, w=120), fps=20.0)
        aq.create_shark(None, anim)
        teeth = next(e for e in anim.entities if e.type == aq.EntityType.TEETH)
        self.assertEqual(teeth.default_color_char, 'R')

    def test_monster_factory_uses_fast_animation_cycle(self):
        """ Monsters should visibly undulate while crossing the screen,
        not wait several seconds between frames. """
        import asciiquarium as aq
        anim = aq.Animation(FakeStdscr(h=30, w=120), fps=20.0)
        aq.create_monster_entity(anim, *aq.get_new_monster_data())
        monster = next(e for e in anim.entities if e.type == aq.EntityType.MONSTER)
        self.assertEqual(monster.default_color_char, 'G')
        self.assertEqual(monster.anim_speed, 0.25)
        self.assertEqual(monster.anim_speed_modifier, 1.0)

    def test_foreground_uses_shape_mask_not_bbox_claim(self):
        """ Foreground occlusion claims the art silhouette, not the full
        rectangle: '?' exterior cells let the back entity show through,
        while an interior blank blocks both foreground and background
        bleed-through. """
        import asciiquarium as aq

        # Fake stdscr that captures every addch into a 2D grid.
        class Cap:
            def __init__(self, h=10, w=20):
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
        front = aq.Entity(
            type='fish',
            shape="X?X\nX X",
            pos=(5, 5, 1),
            occlusion_mask='silhouette',
        )
        back = aq.Entity(
            type='fish',
            shape="BBB\nBBB",
            pos=(5, 5, 2),
            occlusion_mask='visible',
        )
        castle = aq.Entity(
            name='castle',
            shape="CCC\nCCC",
            pos=(5, 5, 22),
        )
        seaweed = aq.Entity(
            type=aq.EntityType.SEAWEED,
            shape="SSS\nSSS",
            pos=(5, 5, 21),
        )
        anim.add_entity(castle)
        anim.add_entity(seaweed)
        anim.add_entity(back)
        anim.add_entity(front)
        anim.draw_screen()

        self.assertEqual(stdscr.grid[5][5], 'X')
        self.assertEqual(stdscr.grid[5][6], 'B')  # '?' did not claim foreground.
        self.assertEqual(stdscr.grid[5][7], 'X')
        self.assertEqual(stdscr.grid[6][5], 'X')
        self.assertEqual(stdscr.grid[6][6], ' ')  # Interior blank erased bg/fg.
        self.assertEqual(stdscr.grid[6][7], 'X')

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
