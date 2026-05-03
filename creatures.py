"""Factories and callbacks for every concrete entity in the tank.

Each create_* function takes an `anim` (the Animation instance), reads
asset data from assets.*, and adds new Entity objects to anim. A few
callbacks (fish_collision, bubble_collision, shark_death, fish_update)
also live here.
"""

from __future__ import annotations

import random
import time
from typing import Callable

from assets import (
    WATER_LINE_SEGMENTS,
    CASTLE_SHAPE, CASTLE_MASK,
    SPLAT_SHAPES,
    SHARK_SHAPES, SHARK_MASKS,
    SHIP_SHAPES, SHIP_MASKS,
    WHALE_SHAPES, WHALE_MASKS, WATER_SPOUT_FRAMES,
    NEW_MONSTER_FRAMES, NEW_MONSTER_MASKS,
    OLD_MONSTER_FRAMES, OLD_MONSTER_MASKS,
    BIG_FISH_1_SHAPES, BIG_FISH_1_MASKS,
    BIG_FISH_2_SHAPES, BIG_FISH_2_MASKS,
    NEW_FISH_DATA, OLD_FISH_DATA,
)
from constants import BASE_FISH_PALETTE, DEPTH, EntityType
from entity import Entity, shape_dimensions


# --- Environment Creation ---
def create_environment(anim: "Animation") -> None:
    water_line_segment_shapes = WATER_LINE_SEGMENTS
    segment_size = len(water_line_segment_shapes[0])
    segment_repeat = anim.width // segment_size + 2

    for i, base_seg in enumerate(water_line_segment_shapes):
        full_seg = (base_seg * segment_repeat)[:anim.width]
        depth_key = f'water_line{i}'
        entity = Entity(
            name=f"water_seg_{i}",
            type=EntityType.WATERLINE,
            shape=full_seg,
            pos=(0, i + 5, DEPTH[depth_key]), # Y position increases downwards
            default_color_char='c', # Cyan
            physical=True, # Bubbles collide with this
        )
        anim.add_entity(entity)

def create_castle(anim: "Animation") -> None:
    castle_image = CASTLE_SHAPE
    castle_mask = CASTLE_MASK
    castle_height = castle_image.count('\n')
    castle_width = max(len(line) for line in castle_image.split('\n'))

    castle_x = max(0, anim.width - castle_width - 1) # Place near right edge
    castle_y = max(0, anim.height - castle_height - 1) # Place near bottom

    entity = Entity(
        name="castle",
        shape=castle_image,
        color_map=castle_mask, # Use the mask directly
        pos=(castle_x, castle_y, DEPTH['castle']),
        default_color_char='y', # Default Yellow for parts not in mask
    )
    anim.add_entity(entity)

# --- Seaweed ---
def create_all_seaweed(anim: "Animation") -> None:
    seaweed_count = max(1, anim.width // 15)
    for _ in range(seaweed_count):
        create_seaweed(None, anim)

def create_seaweed(old_seaweed: Entity | None, anim: "Animation") -> None:
    # This function now acts as both the initial creator and the death callback
    height = random.randint(3, 6)
    seaweed_frames = ['', ''] # Two frames for animation
    for i in range(height):
        left_side = i % 2
        right_side = 1 - left_side
        seaweed_frames[left_side] += " (\n"
        seaweed_frames[right_side] += ")\n"

    # Trim trailing newline
    seaweed_frames = [frame.rstrip() for frame in seaweed_frames]

    seaweed_height = height
    seaweed_width = 2

    x = random.randint(1, max(1, anim.width - seaweed_width - 1))
    y = max(0, anim.height - seaweed_height -1) # Anchor to bottom
    anim_speed = random.uniform(0.25, 0.30) # Time between frames

    # Seaweed lives for 8 to 12 minutes (480 to 720 seconds)
    # 8-12 minutes from now; monotonic so a wall-clock jump doesn't
    # cull or extend living seaweed.
    die_time = time.monotonic() + random.randint(480, 720)

    entity = Entity(
        name='seaweed_' + str(random.randint(100,999)),
        type=EntityType.SEAWEED,
        shape=seaweed_frames, # Animated shape
        pos=(x, y, DEPTH['seaweed']),
        anim_speed=anim_speed,
        die_time=die_time,
        death_cb=create_seaweed, # Respawn when dead
        default_color_char='g', # Green
    )
    anim.add_entity(entity)

# --- Bubbles ---
def create_bubble(fish: Entity, anim: "Animation") -> None:
    fish_w, fish_h = fish.width(), fish.height()
    fish_x, fish_y, fish_z = fish.position()
    fish_vx = fish.vx # Get fish's horizontal speed

    bubble_pos_x = fish_x + fish_w if fish_vx > 0 else fish_x -1 # Bubble starts ahead of moving fish
    bubble_pos_y = fish_y + fish_h // 2
    bubble_pos_z = fish_z - 1 # Bubble on top

    # Match the Perl original: 5 frames where the big O lingers, full
    # upward velocity of 1 cell per tick, and animation interval of 0.1s.
    bubble_shapes = ['.', 'o', 'O', 'O', 'O']

    entity = Entity(
        shape=bubble_shapes,
        type=EntityType.BUBBLE,
        pos=(bubble_pos_x, bubble_pos_y, bubble_pos_z),
        velocity=(0, -1, 0),
        anim_speed=0.1,
        die_offscreen=True,
        physical=True, # Collidable
        coll_handler=bubble_collision,
        default_color_char='C', # Bright Cyan
        die_frame=15, # Die after animating a few times if not popped
    )
    anim.add_entity(entity)

def bubble_collision(bubble: Entity, anim: "Animation") -> None:
    for col_obj in bubble.collisions:
        if col_obj.type == EntityType.WATERLINE:
            bubble.kill()
            break

# --- Fish ---
def create_all_fish(anim: "Animation") -> None:
    # Fish density scales with the underwater area; ~350 cells per fish
    # is the Perl original's heuristic.
    underwater_height = max(1, anim.height - 9)
    fish_count = max(1, (underwater_height * anim.width) // 350)
    for _ in range(fish_count):
        create_fish(None, anim)

def create_fish(old_fish: Entity | None, anim: "Animation") -> None:
    """ Choose between old and new fish styles based on classic mode. """
    if anim.use_new_fish:
        if random.randint(0, 11) > 8:
            create_new_fish_entity(anim)
        else:
            create_old_fish_entity(anim)
    else:
        create_old_fish_entity(anim)

# (Keep add_new_fish_data, add_old_fish_data, add_fish_entity functions separate for clarity)
def get_new_fish_data() -> list:
    return NEW_FISH_DATA

def get_old_fish_data() -> list:
    return OLD_FISH_DATA

def rand_color_mask(color_mask_template: str | None, palette: list[str] | None = None) -> str | None:
    """ Replaces digits 1-9 in a mask template with random color chars.

    `palette` defaults to the original 12-color set; pass anim.fish_palette
    to draw from the extended 256-color set when available.
    """
    if not color_mask_template:
        return None
    colors = palette if palette else BASE_FISH_PALETTE
    mask = color_mask_template
    # Replace numbers (except 4 which is White) with random colors
    for i in range(1, 10):
        if i == 4: continue # Skip 4 (eye color - white)
        color = random.choice(colors)
        mask = mask.replace(str(i), color)
    # Replace 4 with W (White)
    mask = mask.replace('4', 'W')
    return mask


def create_fish_entity(anim: "Animation", fish_data: list) -> None:
    """ Creates a single fish entity from the provided data list. """
    fish_num = random.randrange(len(fish_data))
    shape_l, mask_l, shape_r, mask_r = fish_data[fish_num]

    # Randomly choose direction
    moving_right = random.choice([True, False])

    # Select shape and mask based on direction
    shape = shape_l if moving_right else shape_r  # shape_l is right-facing, shape_r is left-facing
    mask_template = mask_l if moving_right else mask_r

    # Calmer aquarium feel — Perl's [0.25, 2.25] makes fish whiz past too
    # fast at the dt-scaled tick rate, so cap at 1.25.
    speed = random.uniform(0.25, 1.25)
    vx = speed if moving_right else -speed  # Positive for right, negative for left
    vy = 0  # Fish move horizontally

    # Z depth between fish_start and fish_end. Use a continuous float so
    # two fish (which would otherwise tie at one of 18 integer buckets on
    # a populated tank) sort deterministically — fixes the "z-masking"
    # flicker where overlapping fish swap front/back unpredictably.
    z = random.uniform(DEPTH['fish_start'], DEPTH['fish_end'] + 0.999)

    # Create the actual color map from the template
    color_map = rand_color_mask(mask_template, palette=anim.fish_palette)

    # Calculate initial position
    fish_width, fish_height = shape_dimensions(shape)

    # Vertical position constraints
    min_y = 9  # Below waterline
    max_y = max(min_y, anim.height - fish_height - 1)
    y = random.randint(min_y, max_y)

    # Horizontal position: offscreen left for right-moving, right edge for left-moving
    x = -fish_width if moving_right else anim.width - 1

    entity = Entity(
        type=EntityType.FISH,
        shape=shape,
        auto_trans=True,
        color_map=color_map,
        pos=(x, y, z),
        velocity=(vx, vy, 0),
        update_cb=fish_update,  # Custom logic like bubbles
        die_offscreen=True,
        death_cb=create_fish,  # Respawn a new fish when this one dies
        physical=True,
        coll_handler=fish_collision,
        default_color_char='y',  # Default Yellow if mask is incomplete
    )
    anim.add_entity(entity)

def create_new_fish_entity(anim: "Animation") -> None:
     create_fish_entity(anim, get_new_fish_data())

def create_old_fish_entity(anim: "Animation") -> None:
     create_fish_entity(anim, get_old_fish_data())

# --- Fish Callbacks ---
def fish_update(fish: Entity, anim: "Animation") -> None:
    """ Custom update logic for fish (e.g., creating bubbles). """
    # Add a bubble occasionally
    if random.randint(0, 100) > 97:
        create_bubble(fish, anim)

def fish_collision(fish: Entity, anim: "Animation") -> None:
    """ Fish collision handler. """
    for col_obj in fish.collisions:
         # Only check collision with 'teeth' type (from shark)
        if col_obj.type == EntityType.TEETH:
            # Smaller fish get eaten
            if fish.height() <= 5:
                 create_splat(anim, *fish.position()) # Create blood splat
                 fish.kill()
                 break # Fish is dead, stop checking

# --- Splat Effect ---
def create_splat(anim: "Animation", x: float, y: float, z: float, splat_char: str = '*') -> None:
    if splat_char == '*':
        splat_shapes = SPLAT_SHAPES
    else:
        splat_shapes = [s.replace('*', splat_char) for s in SPLAT_SHAPES]

    splat_x = x - 4 # Center the splat approx where the fish was
    splat_y = y - 2
    splat_z = z - 2 # Slightly in front of original fish

    entity = Entity(
        shape=splat_shapes,
        pos=(splat_x, splat_y, splat_z),
        default_color_char='R', # Bright Red
        anim_speed=0.25, # How fast the splat animates
        transparent_char=' ',
        die_frame=15, # Match Perl: die after ~15 anim ticks (cycles through frames a few times)
    )
    anim.add_entity(entity)

# --- Shark ---
def create_shark(old_ent: Entity | None, anim: "Animation") -> None:
    shark_image = SHARK_SHAPES
    shark_mask = SHARK_MASKS

    dir = random.randrange(2) # 0 = left, 1 = right
    shark_shape = shark_image[dir]
    shark_mask_str = shark_mask[dir]
    shark_height = shark_shape.count('\n')
    shark_width = max(len(line) for line in shark_shape.split('\n'))

    speed = 2.0
    vx = speed if dir == 0 else -speed
    vy = 0

    # Y position constraints (allow space for shape)
    min_y = 9 # Below waterline
    max_y = max(min_y, anim.height - shark_height - 1)
    y = random.randint(min_y, max_y)

    # X position (start offscreen)
    x = -shark_width if dir == 0 else anim.width

    # Teeth column lands inside the mouth cluster of the *Python* shark
    # art (`.((` / `(|/|/|/|/` for dir=0 around col 47-49; `\|\|\|\|`
    # for dir=1 around col 4-12). Y offset is the row holding the teeth
    # glyphs in both shapes.
    teeth_offset_x = 48 if dir == 0 else 8
    teeth_offset_y = 7
    teeth_x = x + teeth_offset_x
    teeth_y = y + teeth_offset_y

    # Create teeth entity (invisible, used for collision). Note: do NOT
    # set die_offscreen=True here. The teeth is a 1-char entity but
    # starts offscreen with the shark (which is ~60 chars wide and only
    # partially onscreen). die_offscreen would kill the teeth before its
    # first move, so the shark would never bite anything. Death is
    # driven by the shark's death callback instead.
    teeth = Entity(
        type=EntityType.TEETH,
        shape="*",
        pos=(teeth_x, teeth_y, DEPTH['shark'] + 1),
        velocity=(vx, vy, 0),
        physical=True,
    )
    anim.add_entity(teeth)

    # Create shark entity
    shark = Entity(
        type=EntityType.SHARK,
        shape=shark_shape,
        color_map=shark_mask_str,
        auto_trans=True,
        pos=(x, y, DEPTH['shark']),
        default_color_char='W', # Match Perl: bright white default
        velocity=(vx, vy, 0),
        die_offscreen=True,
        death_cb=shark_death, # Custom death handler
        death_cb_args=[teeth], # Pass teeth entity to death callback
    )
    anim.add_entity(shark)


def shark_death(shark: Entity, anim: "Animation", teeth_entity: Entity | None) -> None:
    """ Shark death callback: kill the associated teeth entity and spawn a new random object. """
    if teeth_entity:
         teeth_entity.kill()
    # Spawn a new random object to replace the shark
    create_random_object(shark, anim)


# --- Ship ---
def create_ship(old_ent: Entity | None, anim: "Animation") -> None:
    ship_image = SHIP_SHAPES
    ship_mask = SHIP_MASKS

    dir = random.randrange(2) # 0 = left, 1 = right
    shape = ship_image[dir]
    mask = ship_mask[dir]
    ship_height = shape.count('\n')
    ship_width = max(len(line) for line in shape.split('\n'))

    speed = 1.0
    vx = speed if dir == 0 else -speed
    vy = 0
    y = 0 # At the top of the screen

    # X position (start offscreen)
    x = -ship_width if dir == 0 else anim.width

    entity = Entity(
        type=EntityType.SHIP,
        shape=shape,
        color_map=mask,
        auto_trans=True,
        pos=(x, y, DEPTH['water_gap1']), # Z-depth for waterline effect
        default_color_char='Y', # Yellow default
        velocity=(vx, vy, 0),
        die_offscreen=True,
        death_cb=create_random_object, # Spawn next random object
    )
    anim.add_entity(entity)

# --- Whale ---
def create_whale(old_ent: Entity | None, anim: "Animation") -> None:
    whale_image = WHALE_SHAPES
    whale_mask = WHALE_MASKS
    water_spout_frames = WATER_SPOUT_FRAMES

    dir = random.randrange(2) # 0 = left, 1 = right
    base_whale_shape = whale_image[dir]
    base_whale_mask = whale_mask[dir]
    whale_height = base_whale_shape.count('\n')
    whale_width = max(len(line) for line in base_whale_shape.split('\n'))

    speed = 1.0
    vx = speed if dir == 0 else -speed
    vy = 0
    y = 0 # Top of screen

    # X position (start offscreen)
    x = -whale_width - 5 if dir == 0 else anim.width + 5 # Add margin

    # Column offset of the spout — lines up with the blowhole on each
    # whale shape (right-facing whale has the blowhole further right).
    spout_align_x = 11 if dir == 0 else 1

    whale_anim_shapes = []
    whale_anim_masks = []

    # Match the Perl original: 5 silent frames (no spout) followed by
    # the 7 spout-animation frames, so the whale swims a few seconds
    # between exhalations.
    silent_prefix = "\n\n\n" + base_whale_shape.strip('\n')
    for _ in range(5):
        whale_anim_shapes.append(silent_prefix)
        whale_anim_masks.append(base_whale_mask)

    # Then the actual water-spout cycle.
    for spout_frame in water_spout_frames:
         aligned_spout_lines = []
         for line in spout_frame.split('\n'):
             aligned_spout_lines.append(" " * spout_align_x + line)
         aligned_spout = "\n".join(aligned_spout_lines)
         combined_shape = aligned_spout.rstrip('\n') + "\n" + base_whale_shape.strip('\n')
         combined_mask = ("\n" * spout_frame.count('\n')) + base_whale_mask
         whale_anim_shapes.append(combined_shape)
         whale_anim_masks.append(combined_mask)


    entity = Entity(
        type=EntityType.WHALE,
        shape=whale_anim_shapes, # Animated shape list
        color_map=whale_anim_masks, # Animated mask list (basic)
        auto_trans=True,
        pos=(x, y, DEPTH['water_gap2']),
        default_color_char='B', # Blue default
        velocity=(vx, vy, 0, 1.0), # 4th arg = animation speed modifier (1.0 normal)
        anim_speed=0.8, # Time between animation frames (whale/spout cycle)
        die_offscreen=True,
        death_cb=create_random_object,
    )
    anim.add_entity(entity)


# --- Sea Monster ---
def create_monster(old_ent: Entity | None, anim: "Animation") -> None:
    if anim.use_new_monster:
        create_new_monster_entity(anim)
    else:
        create_old_monster_entity(anim)

def get_new_monster_data() -> tuple:
    return NEW_MONSTER_FRAMES, NEW_MONSTER_MASKS

def get_old_monster_data() -> tuple:
    return OLD_MONSTER_FRAMES, OLD_MONSTER_MASKS

def create_monster_entity(anim: "Animation", monster_data: list, monster_mask_data: list) -> None:
    """ Creates a sea monster entity. """
    dir = random.randrange(2) # 0 = left, 1 = right
    shapes = monster_data[dir]
    mask_base = monster_mask_data[dir]
    num_frames = len(shapes)

    # Use the same mask for all frames of a given direction
    masks = [mask_base] * num_frames

    # Calculate dimensions from the first frame
    mon_width, mon_height = shape_dimensions(shapes[0])

    speed = 2.0
    vx = speed if dir == 0 else -speed
    vy = 0
    y = 2 # Fixed Y position near the top

    # X position (start offscreen)
    x = -mon_width if dir == 0 else anim.width

    entity = Entity(
        type=EntityType.MONSTER,
        shape=shapes, # Animated shape list
        color_map=masks, # Basic mask list
        auto_trans=True,
        pos=(x, y, DEPTH['water_gap2']), # Z-depth near whale
        default_color_char='G', # Green default
        velocity=(vx, vy, 0, 0.25), # 4th arg = animation speed modifier
        anim_speed=1.0, # Base time between frames (modified by velocity[3])
        die_offscreen=True,
        death_cb=create_random_object,
    )
    anim.add_entity(entity)

def create_new_monster_entity(anim: "Animation") -> None:
    data, masks = get_new_monster_data()
    create_monster_entity(anim, data, masks)

def create_old_monster_entity(anim: "Animation") -> None:
    data, masks = get_old_monster_data()
    create_monster_entity(anim, data, masks)

# --- Big Fish ---
def create_big_fish(old_ent: Entity | None, anim: "Animation") -> None:
    """ Choose between big_fish_1 and big_fish_2 based on classic mode. """
    if anim.use_new_fish and random.randint(0, 2) > 0:  # 2/3 chance for type 2
        create_big_fish_2(old_ent, anim)
    else:
        create_big_fish_1(old_ent, anim)


def create_big_fish_1(old_ent: Entity | None, anim: "Animation") -> None:
    big_fish_image = BIG_FISH_1_SHAPES
    big_fish_mask = BIG_FISH_1_MASKS

    dir = random.randrange(2) # 0 = left, 1 = right
    shape = big_fish_image[dir]
    mask_template = big_fish_mask[dir] # Mask uses '1' and '2'
    fish_height = shape.count('\n')
    fish_width = max(len(line) for line in shape.split('\n'))

    speed = 3.0
    vx = speed if dir == 0 else -speed
    vy = 0

    # Y position constraints
    min_y = 9
    max_y = max(min_y, anim.height - fish_height - 1)
    y = random.randint(min_y, max_y)

    # X position (start offscreen)
    x = -fish_width if dir == 0 else anim.width

    # Apply random colors to '1' and '2' in the mask
    # Let '1' be the main body color, '2' be the highlight
    colors = anim.fish_palette
    body_color = random.choice(colors)
    highlight_color = random.choice([c for c in colors if c != body_color]) # Different highlight
    color_map = mask_template.replace('1', body_color).replace('2', highlight_color)
    # 'W' for eye remains white

    entity = Entity(
        type=EntityType.BIG_FISH,
        shape=shape,
        color_map=color_map,
        auto_trans=True,
        pos=(x, y, DEPTH['shark']), # Same depth as shark
        default_color_char='Y', # Fallback color
        velocity=(vx, vy, 0),
        die_offscreen=True,
        death_cb=create_random_object,
    )
    anim.add_entity(entity)


def create_big_fish_2(old_ent: Entity | None, anim: "Animation") -> None:
    big_fish_image = BIG_FISH_2_SHAPES
    big_fish_mask = BIG_FISH_2_MASKS

    dir = random.randrange(2) # 0 = left, 1 = right
    shape = big_fish_image[dir]
    mask_template = big_fish_mask[dir] # Mask uses '1' and '2'
    fish_height = shape.count('\n')
    fish_width = max(len(line) for line in shape.split('\n'))

    speed = 2.5
    vx = speed if dir == 0 else -speed
    vy = 0

    # Y position constraints
    min_y = 9
    max_y = max(min_y, anim.height - fish_height - 1)
    y = random.randint(min_y, max_y)

    # X position (start offscreen)
    x = -fish_width if dir == 0 else anim.width

    # Apply random colors to '1' and '2'
    colors = anim.fish_palette
    body_color = random.choice(colors)
    fin_color = random.choice([c for c in colors if c != body_color])
    color_map = mask_template.replace('1', body_color).replace('2', fin_color)
    # 'W' for eye remains white

    entity = Entity(
        type=EntityType.BIG_FISH,
        shape=shape,
        color_map=color_map,
        auto_trans=True,
        pos=(x, y, DEPTH['shark']),
        default_color_char='Y',
        velocity=(vx, vy, 0),
        die_offscreen=True,
        death_cb=create_random_object,
    )
    anim.add_entity(entity)

# --- Random Object Handling ---
RANDOM_OBJECT_POOL = [
    create_ship,
    create_whale,
    create_monster,
    create_big_fish,
    create_shark,
]

def create_random_object(dead_object: Entity | None, anim: "Animation") -> None:
    """ Selects and creates a new random object, usually when one dies offscreen. """
    # The dead_object isn't actually used here, but matches Perl callback signature
    random_func = random.choice(RANDOM_OBJECT_POOL)
    random_func(None, anim) # Call the chosen creation function

