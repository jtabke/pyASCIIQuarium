"""Curses renderer/compositor for the aquarium.

Rendering is deliberately mask-aware: background entities are painted
normally, while foreground entities are composited front-to-back and
claim only their configured occlusion masks.
"""

from __future__ import annotations

import curses
from typing import Any

from constants import EntityType

_BACKGROUND_TYPES = {EntityType.WATERLINE, EntityType.SEAWEED}
_BACKGROUND_NAMES = {'castle'}

_DEBUG_SYMBOLS = {
    'visible': '*',
    'silhouette': '.',
    'collision': '#',
    'occlusion': '+',
    'bbox': '%',
}


def is_background(entity: Any) -> bool:
    """True if an entity should render in the background pass."""
    return entity.type in _BACKGROUND_TYPES or entity.name in _BACKGROUND_NAMES


def draw_screen(anim: Any) -> None:
    """Draw all entities, with mask-based foreground occlusion."""
    anim.stdscr.erase()

    background = []
    foreground = []
    for entity in anim.entities:
        if not entity.is_alive:
            continue
        (background if is_background(entity) else foreground).append(entity)

    # Background: plain painter's algorithm, back-to-front.
    for entity in sorted(background, key=lambda e: e.z, reverse=True):
        draw_entity_no_claim(anim, entity)

    # Foreground: front-to-back mask claims.
    claimed: set[tuple[int, int]] = set()
    for entity in sorted(foreground, key=lambda e: e.z):
        draw_entity_with_claim(anim, entity, claimed)

    draw_debug_masks(anim)

    anim.stdscr.refresh()
    anim.needs_redraw = False


def draw_entity_no_claim(anim: Any, entity: Any) -> None:
    """Painter's-algorithm draw: write each non-transparent cell."""
    lines, color_lines = entity.get_shape_and_colors()
    start_x, start_y = int(entity.x), int(entity.y)
    default_attr = anim.get_color_attr(entity.default_color_char)
    tchar = entity.transparent_char

    for i, line in enumerate(lines):
        current_y = start_y + i
        if not (0 <= current_y < anim.height):
            continue
        color_line = color_lines[i] if i < len(color_lines) else ""
        for j, char in enumerate(line):
            current_x = start_x + j
            if not (0 <= current_x < anim.width):
                continue
            if char == '?' or char == tchar:
                continue
            attr = default_attr
            if j < len(color_line):
                cc = color_line[j]
                if cc != ' ' and cc != '?':
                    attr = anim.get_color_attr(cc)
            try:
                anim.stdscr.addch(current_y, current_x, char, attr)
            except curses.error:
                pass


def draw_entity_with_claim(anim: Any, entity: Any, claimed: set[tuple[int, int]]) -> None:
    """Foreground compositing with shape-mask occlusion."""
    frame = entity.current_sprite_frame()
    start_x, start_y = int(entity.x), int(entity.y)
    default_attr = anim.get_color_attr(entity.default_color_char)

    for i in range(frame.height):
        current_y = start_y + i
        if not (0 <= current_y < anim.height):
            continue
        for j in range(frame.width):
            current_x = start_x + j
            if not (0 <= current_x < anim.width):
                continue
            cell = (current_y, current_x)
            if cell in claimed:
                continue

            occludes = frame.contains(entity.occlusion_mask, j, i)
            if occludes:
                claimed.add(cell)

            if not frame.contains('visible', j, i):
                # Interior silhouette blanks are part of the foreground
                # body: they should hide already-painted background art
                # like the castle. True exterior transparent cells do
                # not occlude and therefore still let background show.
                if occludes:
                    try:
                        anim.stdscr.addch(current_y, current_x, ' ', default_attr)
                    except curses.error:
                        pass
                continue

            char = frame.char_at(j, i)
            attr = default_attr
            cc = frame.color_at(j, i)
            if cc and cc != ' ' and cc != '?':
                attr = anim.get_color_attr(cc)
            try:
                anim.stdscr.addch(current_y, current_x, char, attr)
            except curses.error:
                pass


def draw_debug_masks(anim: Any) -> None:
    """Overlay the selected mask mode for tuning/debugging.

    Toggled at runtime with the `m` key. This is intentionally simple:
    it draws ASCII marker characters over the normal scene.
    """
    mode = getattr(anim, 'debug_mask_mode', None)
    if not mode:
        return

    symbol = _DEBUG_SYMBOLS.get(mode, '?')
    attr = anim.get_color_attr('M')

    for entity in sorted((e for e in anim.entities if e.is_alive), key=lambda e: e.z, reverse=True):
        frame = entity.current_sprite_frame()
        start_x, start_y = int(entity.x), int(entity.y)
        if mode == 'collision':
            mask_mode = entity.collision_mask
        elif mode == 'occlusion':
            mask_mode = entity.occlusion_mask
        else:
            mask_mode = mode

        for i in range(frame.height):
            y = start_y + i
            if not (0 <= y < anim.height):
                continue
            for j in range(frame.width):
                x = start_x + j
                if not (0 <= x < anim.width):
                    continue
                if not frame.contains(mask_mode, j, i):
                    continue
                try:
                    anim.stdscr.addch(y, x, symbol, attr)
                except curses.error:
                    pass

    label = f"mask:{mode}"
    try:
        anim.stdscr.addnstr(0, 0, label, max(0, anim.width - 1), attr)
    except curses.error:
        pass
