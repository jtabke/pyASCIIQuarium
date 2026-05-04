"""Sprite-frame parsing and mask helpers for ASCII art entities.

A frame keeps the original character/color lines, but also precomputes
bitmask rows for the things the engine needs to reason about:

- visible: cells that draw a glyph
- silhouette: cells that belong to the ASCII-art shape, including
  interior blanks, but excluding explicit '?' transparency
- bbox: the full rectangular bounds, for broad-phase checks/fallbacks

The masks let rendering and collision keep the classic ASCII source art
while avoiding "the entity is just its rectangle" behavior.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum


class MaskMode(str, Enum):
    """Named sprite masks used by rendering and collision."""

    NONE = "none"
    BBOX = "bbox"
    VISIBLE = "visible"
    SILHOUETTE = "silhouette"
    SOLID = "solid"  # Alias for SILHOUETTE, kept for readability.


def mask_mode_value(mode: str | MaskMode) -> str:
    """Normalize raw strings and MaskMode enum members."""
    return mode.value if isinstance(mode, MaskMode) else mode


@dataclass(frozen=True)
class SpriteFrame:
    """One parsed ASCII-art frame.

    Bits are stored least-significant-bit first: bit 0 is local x=0,
    bit 1 is local x=1, and so on. Each row integer represents one
    local y coordinate.
    """

    lines: list[str]
    color_lines: list[str]
    width: int
    height: int
    visible_rows: tuple[int, ...]
    silhouette_rows: tuple[int, ...]

    @classmethod
    def parse(
        cls,
        shape_str: str | None,
        color_map_str: str | None = None,
        transparent_char: str = " ",
    ) -> "SpriteFrame":
        """Parse raw shape/color strings into a frame and masks."""
        if not shape_str:
            lines: list[str] = []
        else:
            lines = shape_str.strip("\n").split("\n")

        width = max((len(line) for line in lines), default=0)
        height = len(lines)

        if color_map_str:
            color_lines = color_map_str.strip("\n").split("\n")
        else:
            color_lines = []

        visible_rows: list[int] = []
        silhouette_rows: list[int] = []

        for line in lines:
            visible = 0
            silhouette = 0
            for x, char in enumerate(line):
                bit = 1 << x
                # '?' is the art-level transparent marker inherited
                # from the original Term::Animation assets.
                if char != "?":
                    silhouette |= bit
                # The visual mask only includes cells that actually
                # draw a character. A literal transparent_char (usually
                # space) can still be part of the silhouette if it is an
                # interior blank rather than exterior transparency.
                if char != "?" and char != transparent_char:
                    visible |= bit
            visible_rows.append(visible)
            silhouette_rows.append(silhouette)

        return cls(
            lines=lines,
            color_lines=color_lines,
            width=width,
            height=height,
            visible_rows=tuple(visible_rows),
            silhouette_rows=tuple(silhouette_rows),
        )

    def rows_for(self, mode: str | MaskMode) -> tuple[int, ...]:
        """Return row bitmasks for a named purpose.

        `solid` is accepted as an alias for `silhouette`.
        """
        mode_value = mask_mode_value(mode)
        if mode_value == MaskMode.NONE.value:
            return (0,) * self.height
        if mode_value == MaskMode.BBOX.value:
            full = (1 << self.width) - 1 if self.width > 0 else 0
            return (full,) * self.height
        if mode_value == MaskMode.VISIBLE.value:
            return self.visible_rows
        if mode_value in (MaskMode.SILHOUETTE.value, MaskMode.SOLID.value):
            return self.silhouette_rows
        raise ValueError(f"unknown sprite mask mode: {mode!r}")

    def contains(self, mode: str | MaskMode, x: int, y: int) -> bool:
        """True if local cell `(x, y)` is set in the requested mask."""
        if x < 0 or y < 0 or x >= self.width or y >= self.height:
            return False
        rows = self.rows_for(mode)
        return bool(rows[y] & (1 << x))

    def char_at(self, x: int, y: int, default: str = " ") -> str:
        if y < 0 or y >= len(self.lines):
            return default
        line = self.lines[y]
        if x < 0 or x >= len(line):
            return default
        return line[x]

    def color_at(self, x: int, y: int, default: str = "") -> str:
        if y < 0 or y >= len(self.color_lines):
            return default
        line = self.color_lines[y]
        if x < 0 or x >= len(line):
            return default
        return line[x]


def masks_overlap(
    a_frame: SpriteFrame,
    a_x: int,
    a_y: int,
    a_mode: str | MaskMode,
    b_frame: SpriteFrame,
    b_x: int,
    b_y: int,
    b_mode: str | MaskMode,
) -> tuple[bool, tuple[int, int] | None]:
    """Return whether two placed frame masks overlap.

    The optional point is the first overlapping world cell found. Callers
    can ignore it today, but keeping it here makes future collision
    events/debug overlays straightforward.
    """
    left = max(a_x, b_x)
    right = min(a_x + a_frame.width, b_x + b_frame.width)
    top = max(a_y, b_y)
    bottom = min(a_y + a_frame.height, b_y + b_frame.height)

    if left >= right or top >= bottom:
        return False, None

    width = right - left
    overlap_mask = (1 << width) - 1
    a_rows = a_frame.rows_for(a_mode)
    b_rows = b_frame.rows_for(b_mode)

    for world_y in range(top, bottom):
        a_local_y = world_y - a_y
        b_local_y = world_y - b_y
        a_shift = left - a_x
        b_shift = left - b_x
        a_bits = (a_rows[a_local_y] >> a_shift) & overlap_mask
        b_bits = (b_rows[b_local_y] >> b_shift) & overlap_mask
        hit_bits = a_bits & b_bits
        if hit_bits:
            # Isolate the lowest set bit so the returned point is
            # left-to-right stable.
            lowest = hit_bits & -hit_bits
            hit_x_offset = lowest.bit_length() - 1
            return True, (left + hit_x_offset, world_y)

    return False, None
