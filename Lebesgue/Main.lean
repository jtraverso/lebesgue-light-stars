/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Lebesgue.Discharging
public import Lebesgue.Path4

/-!
# Light `3`-stars in planar graphs of minimum degree five

For a finite simple planar graph of minimum degree at least five (Jendrol' and Madaras):

* `light_star` (Theorem 1): a vertex of degree five with three distinct neighbours of degrees
  `(5, ≤ 6, ≤ 7)` or `(6, 6, 6)`;
* `light_star4` (Theorem 2): a vertex of degree five with four distinct neighbours of degree at
  most ten;
* `light_path4` (Theorem 3): a path on four vertices of weight at most `23`.
-/

@[expose] public section

namespace Lebesgue

open LeanPool.K5MinorFreeChoosability

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem light_star [Nonempty V] (hG : IsPlanar G) (hδ : ∀ v, 5 ≤ G.degree v) :
    ∃ x a₁ a₂ a₃ : V, G.Adj x a₁ ∧ G.Adj x a₂ ∧ G.Adj x a₃ ∧ a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃ ∧
      G.degree x = 5 ∧ ((G.degree a₁ = 5 ∧ G.degree a₂ ≤ 6 ∧ G.degree a₃ ≤ 7) ∨
        (G.degree a₁ = 6 ∧ G.degree a₂ = 6 ∧ G.degree a₃ = 6)) := by
  classical
  by_contra hcon
  refine exists_light_star hG hδ ?_
  intro x a₁ a₂ a₃ h1 h2 h3 h12 h13 h23 hx hp
  exact hcon ⟨x, a₁, a₂, a₃, h1, h2, h3, h12, h13, h23, hx, hp⟩

theorem light_star4 [Nonempty V] (hG : IsPlanar G) (hδ : ∀ v, 5 ≤ G.degree v) :
    ∃ x a₁ a₂ a₃ a₄ : V, G.Adj x a₁ ∧ G.Adj x a₂ ∧ G.Adj x a₃ ∧ G.Adj x a₄ ∧ a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧
      a₁ ≠ a₄ ∧ a₂ ≠ a₃ ∧ a₂ ≠ a₄ ∧ a₃ ≠ a₄ ∧ G.degree x = 5 ∧ G.degree a₁ ≤ 10 ∧
      G.degree a₂ ≤ 10 ∧ G.degree a₃ ≤ 10 ∧ G.degree a₄ ≤ 10 := by
  classical
  by_contra hcon
  refine LightStar4.exists_light_star4 hG hδ ?_
  intro x a₁ a₂ a₃ a₄ h1 h2 h3 h4 h12 h13 h14 h23 h24 h34 hx hp
  exact hcon ⟨x, a₁, a₂, a₃, a₄, h1, h2, h3, h4, h12, h13, h14, h23, h24, h34, hx, hp⟩

theorem light_path4 [Nonempty V] (hG : IsPlanar G) (hδ : ∀ v, 5 ≤ G.degree v) :
    ∃ a b c d : V, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧ G.Adj a b ∧ G.Adj b c ∧
      G.Adj c d ∧ G.degree a + G.degree b + G.degree c + G.degree d ≤ 23 := by
  classical
  by_contra hcon
  refine LightPath4.exists_light_path4 hG hδ ?_
  intro a b c d h1 h2 h3 h4 h5 h6 h7 h8 h9
  by_contra hw
  exact hcon ⟨a, b, c, d, h1, h2, h3, h4, h5, h6, h7, h8, h9, by omega⟩

end Lebesgue
