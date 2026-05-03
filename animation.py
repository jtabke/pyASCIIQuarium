"""Animation engine: input loop, draw, collision, frame timing.

Owns the curses screen, the entity list, color-pair table, and the
classic-mode toggles. Calls into creatures.* to populate or rebuild
the tank — those are the only outward dependencies.
"""

from __future__ import annotations

import curses
import random
import time

from constants import (
    BASE_FISH_PALETTE, COLOR_CHAR_MAP, EXTENDED_COLOR_MAP, EntityType, VERSION,
)
from creatures import (
    RANDOM_OBJECT_POOL,
    create_all_fish, create_all_seaweed, create_castle, create_environment,
    create_fish,
)
from entity import Entity


# --- Animation Class ---
class Animation:
    def __init__(
        self,
        stdscr,
        classic_mode: bool = False,
        fps: float = 20.0,
        use_color: bool = True,
    ) -> None:
        self.stdscr = stdscr
        self.height, self.width = stdscr.getmaxyx()
        self.entities = []
        self.paused = False
        self.needs_redraw = True # Flag to force redraw after resize etc.
        self.classic_mode = classic_mode
        # Classic mode disables both the expanded fish set and the
        # newer-style sea monster (these are the only "new" features
        # the original Perl asciiquarium gates on the same flag).
        self.use_new_fish = not classic_mode
        self.use_new_monster = not classic_mode
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


    def get_color_attr(self, color_char: str) -> int:
        """ curses attr for a color char, falling back to the default pair. """
        return self.color_pairs.get(color_char, self.color_pairs.get(color_char.lower(), self.color_pairs['default']))

    def add_entity(self, entity: Entity) -> None:
        self.entities.append(entity)
        self.needs_redraw = True

    def remove_entity(self, entity: Entity) -> None:
        try:
            self.entities.remove(entity)
            self.needs_redraw = True
        except ValueError:
            pass

    def get_entities_of_type(self, entity_type: str) -> list[Entity]:
        return [e for e in self.entities if e.type == entity_type]

    def remove_all_entities(self) -> None:
        self.entities = []
        self.needs_redraw = True

    def update_term_size(self) -> bool:
        """ Resync to the current terminal size. Returns True if changed. """
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

    def check_collisions(self) -> None:
        """ Generic axis-aligned bbox overlap among physical entities.

        Each entity opts in via physical=True and decides what to do
        with collisions in its coll_handler (e.g. shark teeth vs fish,
        bubble vs waterline).
        """
        physical = [e for e in self.entities if e.physical and e.is_alive]
        boxes = []
        for e in physical:
            x, y, _ = e.position()
            ix, iy = int(x), int(y)
            boxes.append((ix, iy, ix + e.width(), iy + e.height(), e))

        for i, (ax1, ay1, ax2, ay2, a) in enumerate(boxes):
            for j in range(i + 1, len(boxes)):
                bx1, by1, bx2, by2, b = boxes[j]
                if ax1 < bx2 and bx1 < ax2 and ay1 < by2 and by1 < ay2:
                    if a.coll_handler:
                        a.collisions.append(b)
                    if b.coll_handler:
                        b.collisions.append(a)

    def animate(self) -> None:
        """ Update all entities, run collision handlers, reap the dead. """
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

        # Run collision handlers for entities still alive — these may
        # decide to kill themselves (e.g. a bubble that hits the
        # waterline), which is why we collect dead entities AFTER
        # this pass rather than before.
        for entity in self.entities:
            if entity.is_alive:
                entity.handle_collisions(self)

        dead_entities = [e for e in self.entities if not e.is_alive]
        for entity in dead_entities:
            if entity.death_cb:
                entity.death_cb(entity, self, *entity.death_cb_args)
            self.remove_entity(entity) # Remove from list


    def draw_screen(self) -> None:
        """ Draw all entities onto the screen, sorted back-to-front by z. """
        self.stdscr.erase()
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

                             try:
                                  self.stdscr.addch(current_y, current_x, char, attr)
                             except curses.error:
                                  # addch on the bottom-right corner of a
                                  # window is documented to fail; ignore.
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
    _GEOMETRY_TYPES = {EntityType.WATERLINE, EntityType.SEAWEED}
    _GEOMETRY_NAMES = {'castle'}

    def _populate(self) -> None:
        """ Create the static + initial random-object population. """
        create_environment(self)
        create_castle(self)
        create_all_seaweed(self)
        create_all_fish(self)
        RANDOM_OBJECT_POOL[random.randrange(len(RANDOM_OBJECT_POOL))](None, self)
        self.paused = False
        self.needs_redraw = True

    def _rebuild_geometry(self) -> None:
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
        current = sum(1 for e in self.entities if e.type == EntityType.FISH)
        for _ in range(max(0, target - current)):
            create_fish(None, self)
        self.needs_redraw = True

    def _too_small(self) -> bool:
        return self.height < self.MIN_HEIGHT or self.width < self.MIN_WIDTH

    def _show_too_small(self) -> None:
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

    def run(self) -> None:
        """ Main animation loop. """
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
