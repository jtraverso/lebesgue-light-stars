# Light stars and paths in planar graphs of minimum degree five in Lean 4

Author and maintainer: **Juan Pablo Traverso Gianini**. Licence: Apache-2.0 (see `LICENSE`).

A Lean 4 / Mathlib formalization of Theorems 1, 2 and 3 of S. Jendrol' and T. Madaras, *On light
subgraphs in plane graphs of minimum degree five*, Discuss. Math. Graph Theory 16 (1996) 207–217
([doi:10.7151/dmgt.1035](https://doi.org/10.7151/dmgt.1035)).

| Lean (namespace `LebesgueTheorem`) | Statement |
|---|---|
| `light_star` | Theorem 1: a finite simple planar graph of minimum degree at least five has a vertex `X` of degree five with three distinct neighbours `A₁, A₂, A₃` such that `deg A₁ = 5`, `deg A₂ ≤ 6`, `deg A₃ ≤ 7`, or `deg A₁ = deg A₂ = deg A₃ = 6`. |
| `light_star4` | Theorem 2: it has a vertex of degree five with four distinct neighbours of degree at most `10`. |
| `light_path4` | Theorem 3: it has a path on four vertices whose degrees sum to at most `23`. |

In particular there is a `5`-vertex with three neighbours of degree at most seven (a light star
in the sense of Lebesgue, 1940). The bounds `6`, `7`, `10` and `23` are best possible; the examples
are not formalized.

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

**Theorem 2** (`Lebesgue/Star4.lean`). Vertices of degree at least `12` send `1/2` to each
`5`-neighbour; an `11`-vertex `A` sends `1/2` to a `5`-neighbour `X` unless, in the rotation at
`X` from `A`, the two neighbours next to `A` are `5`-vertices and either the next two have degree
at least `11` (the article's exception) or the corner after the next one is not on a triangle (the
extension to faces of length at least four). A `5`-vertex receives at least `1` in each of `32768`
configurations (`LightStar4.recv4_check`, by `decide`). An `11`-vertex whose eleven neighbours
are `5`-vertices on triangles has an exceptional neighbour: otherwise the outer neighbours of its
link would alternate between degree at least `11` and at most `10` around a cycle of length
eleven (`LightStar4.no_ring`, `LightStar4.parity_check`).

**Theorem 3** (`Lebesgue/Path4.lean`). Vertices of degree `7`, `8` and at least `9` send `1/3`,
`1/2` and `1/3` to each `5`-neighbour; faces of length at least four give `1/2` per corner. This
replaces the article's rule `(deg A - 6)/m(A)`, whose proof needs an edge-maximal counterexample to
be a triangulation. Around a `5`-vertex, the absence of light `4`-paths gives
`dₐ + dᵢ + dᵢ₊₁ ≥ 19` at each triangular corner (paths `nₐ X nᵢ nᵢ₊₁`), and the vertex receives at
least `1` in each of `100000` configurations (`LightPath4.p4_check`, by `decide`). A `7`- or
`8`-vertex with two consecutive `5`-neighbours on a triangle has no other `5`-neighbour (the path
`W A X Y`); otherwise the corners between consecutive `5`-neighbours lie on faces of length at
least four.

## Files

- [`LebesgueChallenge.lean`](LebesgueChallenge.lean): the definitions and the three statements; it
  imports only Mathlib.
- [`LebesgueSolution.lean`](LebesgueSolution.lean): the same definitions, the planarity bridge to
  the Kuratowski library (field by field) and the three theorems.
- `Lebesgue/Local.lean`, `Lebesgue/Discharging.lean` (Theorem 1), `Lebesgue/Star4Local.lean`,
  `Lebesgue/Star4.lean` (Theorem 2), `Lebesgue/Path4Local.lean`, `Lebesgue/Path4.lean`
  (Theorem 3), `Lebesgue/Main.lean`.
- [`comparator.json`](comparator.json), [`formalization.yaml`](formalization.yaml).

## Dependencies

- [`jtraverso/borodin-light-triangles`](https://github.com/jtraverso/borodin-light-triangles) @
  `c85ca2e`, pinned (Palomar submission pending), and through it
  [`jtraverso/kotzig-light-edges`](https://github.com/jtraverso/kotzig-light-edges) @ `0e9f2a2`
  and [`jtraverso/kuratowski`](https://github.com/jtraverso/kuratowski) @ `696ec89`
  (PALOMAR-2026-10-15-000018).

## Not included

The sharpness examples, Theorem 5 and Corollary 4 of the article.

## Checks

Lean `v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`:

```
lake exe cache get
lake build
```

No `sorry`; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound` for the
three theorems; the elaborated statements and definitions of `LebesgueChallenge.lean` and `LebesgueSolution.lean` are
identical (`pp.all`). The Solution export is also accepted by NanoDa and by con-ron
(`--verified`).

The Lean development is AI-written under the author's direction (see `formalization.yaml`).
