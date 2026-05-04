# pyasciiquarium

A Python/curses port of Kirk Baucom's classic Perl
[asciiquarium](http://robobunny.com/projects/asciiquarium) — an animated
ASCII aquarium for your terminal.

```
                             __
                           ( `\
 ,??????????????????????????)   `\
;' `.????????????????????????(     `\__
 ;   `.?????????????__..---''         `~~~~-._
  `.   `.____...--''                         (b `--._
    >                                _.-'     .((     ._    )
  .`.-`--...__             .-'    -.___.....-(|/|/|/|/'
 ;.'?????????`. ...----`.___.',,,_______......---'
 '???????????'-'
```

## Install

```
pip install .
```

`windows-curses` is pulled in automatically on Windows; macOS and Linux
use the stdlib `curses` module.

## Run

```
asciiquarium
```

or, without installing:

```
python3 asciiquarium.py
```

## Controls

| key      | action                  |
|----------|-------------------------|
| `q`      | quit                    |
| `p`      | pause / resume          |
| `r`      | redraw / reshuffle tank |
| `m`      | cycle mask debug overlay |
| `h`, `?` | show in-app help        |

## Flags

```
--classic     classic (original) fish and monster graphics only
--fps N       target frames per second (default: 20)
--no-color    bold/normal attributes only — no color
--seed N      seed the RNG for reproducible runs
--version     print version and exit
```

256-color terminals automatically get an enriched fish palette
(orange, pink, lime, teal, purple, gold) on top of the original 12 colors.

## Layout

- `asciiquarium.py` — thin entry point and public re-exports.
- `animation.py`, `entity.py`, `renderer.py`, `collision.py`, `sprite.py` —
  main loop, entity state, rendering, collision, and parsed ASCII-art masks.
- `assets.py` — every shape and color mask, kept separate so adding a
  new fish doesn't churn the engine file.
- `tests/` — `python3 -m unittest tests.test_smoke` runs the suite.

## Credits

Original Perl asciiquarium © 2003 Kirk Baucom (kbaucom@schizoid.com).
ASCII art largely by Joan Stark and Claudio Matsuoka. Released under
the GNU GPL v2 or later — see `LICENSE`.
