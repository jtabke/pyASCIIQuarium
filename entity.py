"""Entity class: one drawable thing in the tank.

Entity owns its shape, color mask, position/velocity, and lifecycle
callbacks. The Animation engine iterates Entities in animate() and
draw_screen(). Entity itself never calls curses — it just exposes
geometry and the current frame's lines.
"""

from __future__ import annotations

import random
import time
from typing import Any, Callable, Optional, Sequence, Union

from constants import TICK_RATE

Shape = Union[str, list[str]]
Position = tuple[float, float, float]
Velocity = Sequence[float]  # (vx, vy, vz) or (vx, vy, vz, anim_modifier)


def shape_dimensions(shape_str: str | None) -> tuple[int, int]:
    """ (width, height) of a shape string without constructing an Entity.

    Mirrors Entity._update_dimensions: outer newlines are stripped,
    then split on '\\n'. Used by entity factories that need the size
    before placement; allocating a throwaway Entity just to measure
    would also kick off shape preprocessing for nothing.
    """
    if not shape_str:
        return (0, 0)
    lines = shape_str.strip('\n').split('\n')
    return (max((len(line) for line in lines), default=0), len(lines))


# --- Entity Class ---
class Entity:
    def __init__(
        self,
        name: str = "",
        type: str = "",
        shape: Shape | None = None,
        color_map: Shape | None = None,
        pos: Position = (0, 0, 0),
        velocity: Velocity = (0, 0, 0),
        anim_speed: float = 0.0,
        default_color_char: str = 'c',
        die_offscreen: bool = False,
        die_time: float | None = None,
        die_frame: int | None = None,
        death_cb: Optional[Callable[..., Any]] = None,
        death_cb_args: list | None = None,
        update_cb: Optional[Callable[..., Any]] = None,
        update_cb_args: list | None = None,
        coll_handler: Optional[Callable[..., Any]] = None,
        physical: bool = False,
        transparent_char: str = ' ',
        auto_trans: bool = False,
    ) -> None:

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
    def _mark_exterior_transparent(shape_str: str | None) -> str | None:
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

    def _update_dimensions(self) -> None:
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

        color_map_str = self.color_maps[self.current_frame]
        if color_map_str:
            self._color_lines = color_map_str.strip('\n').split('\n')
        else:
            self._color_lines = []

    def get_shape_and_colors(self) -> tuple[list[str], list[str]]:
        """ Lines and color lines for the current frame. """
        return self._lines, self._color_lines

    def width(self) -> int:
        return self._width

    def height(self) -> int:
        return self._height

    def size(self) -> tuple[int, int]:
        return (self._width, self._height)

    def position(self) -> Position:
        return (self.x, self.y, self.z)

    def kill(self) -> None:
        self.is_alive = False

    def update(self, animation_instance: "Animation", dt: float) -> None:
        """ Update entity state (position, animation frame, life status).

        `dt` is the real seconds elapsed since the last animate() call;
        velocities are interpreted in cells per Perl tick (1/TICK_RATE
        seconds), so movement is frame-rate independent.
        """
        if not self.is_alive:
            return

        now = time.monotonic()

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

    def is_offscreen(self, screen_width: int, screen_height: int) -> bool:
        """ True if the entity's bounding box is wholly off the screen. """
        if (self.x + self.width()) <= 0 or self.x >= screen_width:
            return True
        if (self.y + self.height()) <= 0 or self.y >= screen_height:
            return True
        return False

    def handle_collisions(self, animation_instance: "Animation") -> None:
        """ Call the collision handler if any collisions are pending. """
        if self.coll_handler and self.collisions:
            self.coll_handler(self, animation_instance)
        self.collisions = []

