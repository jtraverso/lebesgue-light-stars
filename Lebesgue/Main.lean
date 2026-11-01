/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Lebesgue.Discharging

/-!
# Light `3`-stars in planar graphs of minimum degree five

`light_star`: a finite simple planar graph of minimum degree at least five has a vertex of
degree five with three distinct neighbours of degrees `(5, ≤ 6, ≤ 7)` or `(6, 6, 6)`
(Jendrol' and Madaras, Theorem 1).
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

end Lebesgue
