"""Collision detection for sprite-mask entities.

The engine uses a classic two-phase approach: cheap axis-aligned
bounding boxes as the broad phase, then exact sprite-mask overlap as the
narrow phase. The result is per-entity CollisionEvent objects with an
actual hit point for handlers/debug tooling.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

from sprite import masks_overlap

if TYPE_CHECKING:  # pragma: no cover - imported for type checkers only
    from entity import Entity


@dataclass(frozen=True)
class CollisionEvent:
    """A collision from one entity's point of view."""

    other: "Entity"
    point: tuple[int, int]


def detect_collisions(entities: list["Entity"]) -> list[tuple["Entity", CollisionEvent]]:
    """Return directional collision events for alive physical entities.

    Each colliding pair produces up to two directional events: one for A
    and one for B. Animation decides which events are useful to keep
    based on whether the receiving entity has a collision handler.
    """
    physical = [e for e in entities if e.physical and e.is_alive]
    boxes = []
    for e in physical:
        x, y, _ = e.position()
        ix, iy = int(x), int(y)
        boxes.append((ix, iy, ix + e.width(), iy + e.height(), e))

    events: list[tuple["Entity", CollisionEvent]] = []
    for i, (ax1, ay1, ax2, ay2, a) in enumerate(boxes):
        for j in range(i + 1, len(boxes)):
            bx1, by1, bx2, by2, b = boxes[j]
            if not (ax1 < bx2 and bx1 < ax2 and ay1 < by2 and by1 < ay2):
                continue

            hit, point = masks_overlap(
                a.current_sprite_frame(), ax1, ay1, a.collision_mask,
                b.current_sprite_frame(), bx1, by1, b.collision_mask,
            )
            if not hit or point is None:
                continue

            events.append((a, CollisionEvent(other=b, point=point)))
            events.append((b, CollisionEvent(other=a, point=point)))

    return events
