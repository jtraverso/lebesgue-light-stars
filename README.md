# Light 3-stars in planar graphs of minimum degree five in Lean 4

Author and maintainer: **Juan Pablo Traverso Gianini**. Licence: Apache-2.0 (see `LICENSE`).

A Lean 4 / Mathlib formalization of Theorem 1 of S. Jendrol' and T. Madaras, *On light
subgraphs in plane graphs of minimum degree five*, Discuss. Math. Graph Theory 16 (1996) 207–217
([doi:10.7151/dmgt.1035](https://doi.org/10.7151/dmgt.1035)).

| Lean (namespace `LebesgueTheorem`) | Statement |
|---|---|
| `light_star` | A finite simple planar graph of minimum degree at least five has a vertex `X` of degree five with three distinct neighbours `A₁, A₂, A₃` such that `deg A₁ = 5`, `deg A₂ ≤ 6`, `deg A₃ ≤ 7`, or `deg A₁ = deg A₂ = deg A₃ = 6`. |

In particular there is a `5`-vertex with three neighbours of degree at most seven (a light star
in the sense of Lebesgue, 1940). The bounds `6` and `7` are best possible; the examples are not
formalized.

## Planarity

As in the registered entry
[Kuratowski's theorem](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-15-000018&version=1):
a *plane map* is a rotation system of the darts of `G` of Euler defect `0`; `G` is planar if it
has one. The definitions, from `numClasses` to `IsPlanar`, are copied verbatim from that entry's
`Challenge.lean`.

## The proof

Discharging on the rotation system (`Lebesgue/Discharging.lean`), from the dart-level Euler
formula (total charge `-12 K < 0`) of
[`jtraverso/kotzig-light-edges`](https://github.com/jtraverso/kotzig-light-edges):

- every face of length at least four gives `1/2` to each of its corners;
- a vertex `A` of degree at least seven sends to each `5`-neighbour `X`, through each of the two
  faces on the sides of `AX`, `1/6` (if `deg A = 7`) or `1/4` (if `deg A ≥ 8`) when that face is a
  triangle whose third vertex has degree at least six or is not a triangle, and `0`, resp. `1/8`,
  when the third vertex has degree five.

These are the article's charges for strong, semi-strong and weak neighbours, split over the two
sides of an edge; faces of length at least four replace the triangulation step. A vertex's charge
is a sum over its corners, computed from the cyclic enumeration of its darts. A `5`-vertex
without a light star receives at least `1` in each of `32768` configurations (degrees capped at
eight, corner types), and a `7`-vertex loses at most `1` in each of `16384` configurations; both
checks (`Lebesgue.recv_check`, `Lebesgue.send7_check`) are proved by `decide`
(`Lebesgue/Local.lean`). A vertex of degree `k ≥ 8` loses at most `1/4` per corner.

## Files

- [`LebesgueChallenge.lean`](LebesgueChallenge.lean): the definitions and the statement; it imports
  only Mathlib.
- [`LebesgueSolution.lean`](LebesgueSolution.lean): the same definitions, the planarity bridge to
  the Kuratowski library (field by field) and the theorem.
- `Lebesgue/Local.lean`, `Lebesgue/Discharging.lean`, `Lebesgue/Main.lean`.
- [`comparator.json`](comparator.json), [`formalization.yaml`](formalization.yaml).

## Dependencies

- [`jtraverso/borodin-light-triangles`](https://github.com/jtraverso/borodin-light-triangles) @
  `c85ca2e`, pinned (Palomar submission pending), and through it
  [`jtraverso/kotzig-light-edges`](https://github.com/jtraverso/kotzig-light-edges) @ `0e9f2a2`
  and [`jtraverso/kuratowski`](https://github.com/jtraverso/kuratowski) @ `696ec89`
  (PALOMAR-2026-10-15-000018).

## Not included

The sharpness examples, and Theorems 2 (light `4`-stars), 3 (light `4`-paths) and 5 and Corollary
4 of the article.

## Checks

Lean `v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`:

```
lake exe cache get
lake build
```

No `sorry`; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`; the
elaborated statements and definitions of `LebesgueChallenge.lean` and `LebesgueSolution.lean` are
identical (`pp.all`).

The Lean development is AI-written under the author's direction (see `formalization.yaml`).
