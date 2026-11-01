/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Lebesgue.Discharging
public import Lebesgue.Star4Local

/-!
# Light `4`-stars in plane maps of minimum degree five

Let `M` be a plane map of a finite simple graph of minimum degree at least five in which no
`5`-vertex has four distinct neighbours of degree at most ten (`NoStar4`), so that every
`5`-vertex has at least two neighbours of degree at least eleven. Move charge as follows:

* every face of length at least four gives `1/2` to each of its corners;
* every vertex of degree at least twelve sends `1/2` to each `5`-neighbour;
* a vertex `A` of degree eleven sends `1/2` to each `5`-neighbour `X`, except when, in the
  rotation at `X` starting from `A`, the two neighbours next to `A` are `5`-vertices and either
  the following two have degree at least eleven or the corner after the next one is not on a
  triangle (`exc`).

This is Rule 2 of Jendrol' and Madaras with the exception extended to faces of length at least
four. `5`-vertices receive at least `1` (`LightStar4.one_le_recv4`). An `11`-vertex whose eleven
neighbours are `5`-vertices on triangles has an exceptional neighbour: otherwise the outer
neighbours of its link would alternate between degree at least eleven and at most ten around a
cycle of length eleven (`no_ring`, `LightStar4.parity_check`).
-/

@[expose] public section

namespace LightStar4

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Kotzig Borodin Lebesgue

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- No `5`-vertex has four distinct neighbours of degree at most ten. -/
def NoStar4 : Prop :=
  ∀ x a₁ a₂ a₃ a₄ : V, G.Adj x a₁ → G.Adj x a₂ → G.Adj x a₃ → G.Adj x a₄ → a₁ ≠ a₂ → a₁ ≠ a₃ →
    a₁ ≠ a₄ → a₂ ≠ a₃ → a₂ ≠ a₄ → a₃ ≠ a₄ → G.degree x = 5 →
    ¬ (G.degree a₁ ≤ 10 ∧ G.degree a₂ ≤ 10 ∧ G.degree a₃ ≤ 10 ∧ G.degree a₄ ≤ 10)

variable (M : PlaneMap G)

/-- The exception of an `11`-vertex `A` toward a `5`-vertex `X`, seen from the dart `d : X → A`. -/
def exc (d : G.Dart) : Prop :=
  G.degree (M.rot d).snd = 5 ∧ G.degree (M.rot⁻¹ d).snd = 5 ∧
    ((11 ≤ G.degree ((M.rot ^ 2) d).snd ∧ 11 ≤ G.degree ((M.rot ^ 3) d).snd) ∨
      fLen M (M.rot d).symm ≠ 3)

noncomputable instance (d : G.Dart) : Decidable (exc M d) := by
  unfold exc
  infer_instance

/-- What the tail of `e` sends to its head. -/
noncomputable def g4 (e : G.Dart) : ℚ :=
  if G.degree e.snd = 5 then
    (if 12 ≤ G.degree e.fst then 1 / 2
      else if G.degree e.fst = 11 then (if exc M e.symm then 0 else 1 / 2) else 0)
  else 0

theorem g4_nonneg (e : G.Dart) : 0 ≤ g4 M e := by
  unfold g4
  split_ifs <;> norm_num

theorem g4_le (e : G.Dart) : g4 M e ≤ 1 / 2 := by
  unfold g4
  split_ifs <;> norm_num

theorem sum_split4 :
    ∑ d : G.Dart, ((1 - 6 / (G.degree d.fst : ℚ)) + (2 - 6 / (fLen M d : ℚ))) =
      ∑ d : G.Dart, ((1 - 6 / (G.degree d.fst : ℚ)) + g4 M d.symm - g4 M d + bigF M d.symm) +
      ∑ x : G.Dart, ((2 - 6 / (fLen M x : ℚ)) - bigF M x) := by
  have h1 : ∑ d : G.Dart, g4 M d.symm = ∑ d : G.Dart, g4 M d :=
    Equiv.sum_comp (dartSymm G) (g4 M)
  have h2 : ∑ d : G.Dart, bigF M d.symm = ∑ d : G.Dart, bigF M d :=
    Equiv.sum_comp (dartSymm G) (bigF M)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [h1, h2]
  ring

/-! ### Rotations at a `5`-vertex -/

theorem rot_pow_five {d : G.Dart} (h5 : G.degree d.fst = 5) : (M.rot ^ 5) d = d := by
  have := pow_card_cls M.rot d
  rwa [card_cls_rot M d, h5] at this

theorem rot_pow_snd_ne {d : G.Dart} (h5 : G.degree d.fst = 5) {i j : ℕ} (hij : i < j)
    (hj : j < 5) : ((M.rot ^ i) d).snd ≠ ((M.rot ^ j) d).snd := by
  intro hs
  have hd : (M.rot ^ i) d = (M.rot ^ j) d := by
    rw [SimpleGraph.Dart.ext_iff]
    exact Prod.ext ((fst_rot_pow M d i).trans (fst_rot_pow M d j).symm) hs
  have hp : (M.rot ^ (j - i)) d = d := by
    apply (M.rot ^ i).injective
    rw [← Perm.mul_apply, ← pow_add, Nat.add_sub_cancel' hij.le]
    exact hd.symm
  have := card_cls_le_of_pow M.rot d (by omega) hp
  rw [card_cls_rot M d, h5] at this
  omega

theorem rot_inv_eq {d : G.Dart} (h5 : G.degree d.fst = 5) : M.rot⁻¹ d = (M.rot ^ 4) d := by
  rw [Perm.inv_eq_iff_eq, ← Perm.mul_apply, ← pow_succ', rot_pow_five M h5]

/-- `NoStar4` at a `5`-vertex, along the rotation from a dart `d`. -/
theorem not_four_small (hns : NoStar4 (G := G)) {d : G.Dart} (h5 : G.degree d.fst = 5)
    {i₁ i₂ i₃ i₄ : ℕ} (h12 : i₁ < i₂) (h23 : i₂ < i₃) (h34 : i₃ < i₄) (h4 : i₄ < 5) :
    ¬ (G.degree ((M.rot ^ i₁) d).snd ≤ 10 ∧ G.degree ((M.rot ^ i₂) d).snd ≤ 10 ∧
      G.degree ((M.rot ^ i₃) d).snd ≤ 10 ∧ G.degree ((M.rot ^ i₄) d).snd ≤ 10) := by
  have hadj : ∀ i, G.Adj d.fst ((M.rot ^ i) d).snd := fun i => by
    have := ((M.rot ^ i) d).adj
    rwa [fst_rot_pow] at this
  exact hns d.fst _ _ _ _ (hadj i₁) (hadj i₂) (hadj i₃) (hadj i₄)
    (rot_pow_snd_ne M h5 h12 (by omega)) (rot_pow_snd_ne M h5 (by omega) (by omega))
    (rot_pow_snd_ne M h5 (by omega) h4) (rot_pow_snd_ne M h5 h23 (by omega))
    (rot_pow_snd_ne M h5 (by omega) h4) (rot_pow_snd_ne M h5 h34 h4) h5

theorem not_four_small_e (hns : NoStar4 (G := G)) (e : ℕ → G.Dart)
    (hrot : ∀ i, (M.rot ^ i) (e 0) = e i) (h5 : G.degree (e 0).fst = 5)
    {i₁ i₂ i₃ i₄ : ℕ} (h12 : i₁ < i₂) (h23 : i₂ < i₃) (h34 : i₃ < i₄) (h4 : i₄ < 5) :
    ¬ (G.degree (e i₁).snd ≤ 10 ∧ G.degree (e i₂).snd ≤ 10 ∧
      G.degree (e i₃).snd ≤ 10 ∧ G.degree (e i₄).snd ≤ 10) := by
  rw [← hrot i₁, ← hrot i₂, ← hrot i₃, ← hrot i₄]
  exact not_four_small M hns h5 h12 h23 h34 h4

/-! ### The ring around an `11`-vertex -/

theorem no_ring (hδ : ∀ v, 5 ≤ G.degree v) (hns : NoStar4 (G := G)) (e : ℕ → G.Dart)
    (hsucc : ∀ n, e (n + 1) = M.rot (e n)) (hper : ∀ n, e (n + 11) = e n)
    (h5 : ∀ n, G.degree (e n).snd = 5) (h3 : ∀ n, fLen M (e n).symm = 3)
    (hexc : ∀ n, ¬ exc M (e n).symm) : False := by
  have hδ2 : ∀ v, 2 ≤ G.degree v := fun v => by have := hδ v; omega
  -- `u n = rot (e n).symm`, the dart from `X n` to `X (n - 1)`
  have hX5 : ∀ n, G.degree (e n).symm.fst = 5 := fun n => h5 n
  have hu1 : ∀ n, M.facePerm (M.facePerm (e n).symm) = M.rot (e (n + 1)).symm := fun n => by
    rw [← rot_eq, ← hsucc, M.facePerm_apply]
  have hu_snd : ∀ n, (M.rot (e (n + 1)).symm).snd = (e n).snd := fun n => by
    rw [← hu1]
    exact third_tri M (h3 n)
  have hu_rot : ∀ n, M.rot (M.rot (e (n + 1)).symm).symm = (e n).symm := fun n => by
    have h3x := pow_card_cls M.facePerm (e n).symm
    unfold fLen at h3
    rw [h3 n] at h3x
    have e3 : M.facePerm (M.facePerm (M.facePerm (e n).symm)) = (e n).symm := by
      simpa [pow_three] using h3x
    rw [hu1] at e3
    rw [← M.facePerm_apply]
    exact e3
  -- the conditions of the exception that always hold
  have hprev : ∀ n, G.degree (M.rot (e n).symm).snd = 5 := fun n => by
    rw [← hper n, show n + 11 = (n + 10) + 1 by ring, hu_snd]
    exact h5 _
  have hnext : ∀ n, G.degree (M.rot⁻¹ (e n).symm).snd = 5 := fun n => by
    have : M.rot⁻¹ (e n).symm = (M.rot (e (n + 1)).symm).symm := by
      rw [Perm.inv_eq_iff_eq, hu_rot]
    rw [this]
    change G.degree (M.rot (e (n + 1)).symm).fst = 5
    rw [M.isRotationSystem.fst_apply]
    exact h5 _
  have hface : ∀ n, fLen M (M.rot (e n).symm).symm = 3 := fun n => by
    by_contra hne
    exact hexc n ⟨hprev n, hnext n, Or.inr hne⟩
  have hnotboth : ∀ n, ¬ (11 ≤ G.degree ((M.rot ^ 2) (e n).symm).snd ∧
      11 ≤ G.degree ((M.rot ^ 3) (e n).symm).snd) := fun n hb =>
    hexc n ⟨hprev n, hnext n, Or.inl hb⟩
  -- sharing: the third neighbour after `A` at `X n` is the second one at `X (n + 1)`
  have hshare : ∀ n, ((M.rot ^ 3) (e n).symm).snd = ((M.rot ^ 2) (e (n + 1)).symm).snd := by
    intro n
    set y := (M.rot (e (n + 1)).symm).symm with hy
    have hy3 : fLen M y = 3 := hface (n + 1)
    have hφy : M.facePerm y = M.rot (M.rot (e (n + 1)).symm) := by
      rw [hy, M.facePerm_apply, SimpleGraph.Dart.symm_symm]
    have hφ3 : M.facePerm (M.facePerm (M.facePerm y)) = y := by
      have h3x := pow_card_cls M.facePerm y
      unfold fLen at hy3
      rw [hy3] at h3x
      simpa [pow_three] using h3x
    have hz : M.rot (M.facePerm (M.facePerm y)).symm = y := by
      rw [← M.facePerm_apply]
      exact hφ3
    have hz5 : G.degree (M.facePerm (M.facePerm y)).symm.fst = 5 := by
      change G.degree (M.facePerm (M.facePerm y)).snd = 5
      rw [third_tri M hy3, hy]
      change G.degree (M.rot (e (n + 1)).symm).snd = 5
      rw [hu_snd]
      exact h5 n
    have hrot2 : (M.rot ^ 2) (M.facePerm (M.facePerm y)).symm = (e n).symm := by
      rw [pow_two, Perm.mul_apply, hz, hy, hu_rot]
    have hrot3 : (M.rot ^ 3) (e n).symm = (M.facePerm (M.facePerm y)).symm := by
      rw [← hrot2, ← Perm.mul_apply, ← pow_add]
      exact rot_pow_five M hz5
    rw [hrot3]
    change (M.facePerm (M.facePerm y)).fst = _
    rw [fst_facePerm, hφy, pow_two, Perm.mul_apply]
  -- at each `X n`, exactly one of the two outer neighbours has degree at least eleven
  have hone : ∀ n, 11 ≤ G.degree ((M.rot ^ 2) (e n).symm).snd ∨
      11 ≤ G.degree ((M.rot ^ 3) (e n).symm).snd := by
    intro n
    by_contra hcon
    push Not at hcon
    have h1 : G.degree ((M.rot ^ 1) (e n).symm).snd ≤ 10 := by rw [pow_one, hprev n]; omega
    have h4 : G.degree ((M.rot ^ 4) (e n).symm).snd ≤ 10 := by
      rw [← rot_inv_eq M (hX5 n), hnext n]; omega
    exact not_four_small M hns (hX5 n) (by norm_num : 1 < 2) (by norm_num : 2 < 3)
      (by norm_num : 3 < 4) (by norm_num : 4 < 5) ⟨h1, by omega, by omega, h4⟩
  set b : ℕ → Bool := fun n => decide (11 ≤ G.degree ((M.rot ^ 2) (e n).symm).snd) with hb
  have hne : ∀ n, (b n != b (n + 1)) = true := by
    intro n
    have := hone n
    have := hnotboth n
    rw [hshare n] at *
    simp only [hb, bne_iff_ne, ne_eq, decide_eq_decide]
    tauto
  have hb11 : b 11 = b 0 := by
    simp only [hb]
    rw [show e 11 = e 0 from hper 0]
  have := parity_check (b 0) (b 1) (b 2) (b 3) (b 4) (b 5) (b 6) (b 7) (b 8) (b 9) (b 10)
  have e0 : (b 0 != b 1) = true := hne 0
  have e1 : (b 1 != b 2) = true := hne 1
  have e2 : (b 2 != b 3) = true := hne 2
  have e3 : (b 3 != b 4) = true := hne 3
  have e4 : (b 4 != b 5) = true := hne 4
  have e5 : (b 5 != b 6) = true := hne 5
  have e6 : (b 6 != b 7) = true := hne 6
  have e7 : (b 7 != b 8) = true := hne 7
  have e8 : (b 8 != b 9) = true := hne 8
  have e9 : (b 9 != b 10) = true := hne 9
  have e10 : (b 10 != b 0) = true := by
    have h := (show (b 10 != b 11) = true from hne 10)
    rwa [hb11] at h
  rw [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10] at this
  exact absurd this (by decide)

/-! ### Vertices -/

theorem vertex4_nonneg (hδ : ∀ v, 5 ≤ G.degree v) (hns : NoStar4 (G := G)) (v : V) :
    0 ≤ ∑ d ∈ Finset.univ.filter (fun d : G.Dart => d.fst = v),
      ((1 - 6 / (G.degree d.fst : ℚ)) + g4 M d.symm - g4 M d + bigF M d.symm) := by
  have hδ2 : ∀ v, 2 ≤ G.degree v := fun v => by have := hδ v; omega
  set F := Finset.univ.filter (fun d : G.Dart => d.fst = v) with hF
  have hFk : F.card = G.degree v := G.dart_fst_fiber_card_eq_degree v
  have hk5 : 5 ≤ G.degree v := hδ v
  have hkpos : (0 : ℚ) < G.degree v := by exact_mod_cast (by omega : 0 < G.degree v)
  have hmemF : ∀ d ∈ F, d.fst = v := fun d hd => (Finset.mem_filter.1 hd).2
  have hbig0 : ∀ d : G.Dart, 0 ≤ bigF M d := fun d => by unfold bigF; split_ifs <;> norm_num
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hA : ∑ d ∈ F, (1 - 6 / (G.degree d.fst : ℚ)) = G.degree v - 6 := by
    rw [Finset.sum_congr rfl (fun d hd => show (1 - 6 / (G.degree d.fst : ℚ)) =
      1 - 6 / (G.degree v : ℚ) by rw [hmemF d hd]), Finset.sum_const, hFk, nsmul_eq_mul]
    field_simp
  rw [hA]
  have hB0 : 0 ≤ ∑ d ∈ F, bigF M d.symm := Finset.sum_nonneg (fun d _ => hbig0 _)
  have hsend0 : G.degree v ≤ 10 → ∑ d ∈ F, g4 M d = 0 := fun h =>
    Finset.sum_eq_zero (fun d hd => by
      unfold g4
      rw [hmemF d hd]
      simp [show ¬ 12 ≤ G.degree v by omega, show G.degree v ≠ 11 by omega])
  have hrecv0 : G.degree v ≠ 5 → ∑ d ∈ F, g4 M d.symm = 0 := fun h =>
    Finset.sum_eq_zero (fun d hd => by
      unfold g4
      rw [show d.symm.snd = v from hmemF d hd, if_neg h])
  have hgle : ∑ d ∈ F, g4 M d ≤ F.card • (1 / 2 : ℚ) :=
    Finset.sum_le_card_nsmul F _ _ (fun d _ => g4_le M d)
  rw [hFk, nsmul_eq_mul] at hgle
  obtain ⟨e, hsucc, hper0, hfst, hinj, himg⟩ := enum M v (by omega)
  have hsumF : ∀ f : G.Dart → ℚ, ∑ d ∈ F, f d = ∑ n ∈ Finset.range (G.degree v), f (e n) :=
    fun f => by rw [show F = _ from himg.symm, Finset.sum_image hinj]
  have hper : ∀ n, e (n + G.degree v) = e n := by
    intro n
    induction n with
    | zero => simpa using hper0
    | succ n ih => rw [show n + 1 + G.degree v = (n + G.degree v) + 1 by ring, hsucc, ih, hsucc]
  have h3 : ∀ n, 3 ≤ fLen M (e n).symm := fun n => three_le_fLen M hδ2 _
  rcases (show G.degree v = 5 ∨ (6 ≤ G.degree v ∧ G.degree v ≤ 10) ∨ G.degree v = 11 ∨
      12 ≤ G.degree v by omega) with h5 | h610 | h11 | h12
  · -- a `5`-vertex receives at least `1`
    rw [hsend0 (by omega)]
    have hrot : ∀ n m, (M.rot ^ m) (e n) = e (n + m) := by
      intro n m
      induction m with
      | zero => simp
      | succ m ih => rw [pow_succ', Perm.mul_apply, ih, ← add_assoc, hsucc]
    have hinv : ∀ n, M.rot⁻¹ (e n) = e (n + 4) := by
      intro n
      rw [Perm.inv_eq_iff_eq, ← hsucc, show n + 4 + 1 = n + 5 by ring, ← h5, hper]
    have hval : ∀ n, g4 M (e n).symm + bigF M (e n).symm =
        sendQ (G.degree (e (n + 4)).snd) (G.degree (e n).snd) (G.degree (e (n + 1)).snd)
          (G.degree (e (n + 2)).snd) (G.degree (e (n + 3)).snd)
          (decide (fLen M (e (n + 1)).symm = 3)) +
        faceQ (decide (fLen M (e n).symm = 3)) := by
      intro n
      have hX : G.degree (e n).symm.snd = 5 := by
        change G.degree (e n).fst = 5
        rw [hfst, h5]
      have hb : bigF M (e n).symm = faceQ (decide (fLen M (e n).symm = 3)) := by
        unfold bigF faceQ
        by_cases ht : fLen M (e n).symm = 3
        · simp [ht]
        · have := h3 n
          simp [ht, show 4 ≤ fLen M (e n).symm by omega]
      rw [hb]
      congr 1
      have hs : (e n).symm.fst = (e n).snd := rfl
      have hr1 : M.rot (e n) = e (n + 1) := (hsucc n).symm
      unfold g4 sendQ
      rw [if_pos hX, hs]
      by_cases c12 : 12 ≤ G.degree (e n).snd
      · simp [c12]
      by_cases c11 : G.degree (e n).snd = 11
      · simp only [c12, c11, if_false, if_true]
        have hexc : exc M (e n).symm.symm ↔ (G.degree (e (n + 4)).snd = 5 ∧
            G.degree (e (n + 1)).snd = 5 ∧ ((11 ≤ G.degree (e (n + 2)).snd ∧
              11 ≤ G.degree (e (n + 3)).snd) ∨ decide (fLen M (e (n + 1)).symm = 3) = false)) := by
          rw [SimpleGraph.Dart.symm_symm]
          unfold exc
          rw [hinv n, hrot n 2, hrot n 3, hr1, decide_eq_false_iff_not]
          tauto
        by_cases cx : exc M (e n).symm.symm
        · rw [if_pos cx, if_pos (hexc.1 cx)]
        · rw [if_neg cx, if_neg (fun h => cx (hexc.2 h))]
      · simp [c12, c11]
    have hsum : ∑ d ∈ F, g4 M d.symm + ∑ d ∈ F, bigF M d.symm =
        ∑ n ∈ Finset.range 5, (sendQ (G.degree (e (n + 4)).snd) (G.degree (e n).snd)
          (G.degree (e (n + 1)).snd) (G.degree (e (n + 2)).snd) (G.degree (e (n + 3)).snd)
          (decide (fLen M (e (n + 1)).symm = 3)) + faceQ (decide (fLen M (e n).symm = 3))) := by
      rw [← Finset.sum_add_distrib, hsumF, h5]
      exact Finset.sum_congr rfl (fun n _ => hval n)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.reduceAdd] at hsum
    have p5 : ∀ n, e (n + 5) = e n := fun n => by rw [← h5]; exact hper n
    rw [show e 5 = e 0 from p5 0, show e 6 = e 1 from p5 1, show e 7 = e 2 from p5 2,
      show e 8 = e 3 from p5 3] at hsum
    have hns' : four_small (cl4 (G.degree (e 0).snd)) (cl4 (G.degree (e 1).snd))
        (cl4 (G.degree (e 2).snd)) (cl4 (G.degree (e 3).snd)) (cl4 (G.degree (e 4).snd)) =
        false := by
      by_contra hc
      rw [Bool.not_eq_false] at hc
      have hd5 : G.degree (e 0).fst = 5 := by rw [hfst, h5]
      have he : ∀ i, (M.rot ^ i) (e 0) = e i := fun i => by rw [hrot, zero_add]
      have key := four_small_cl4 hc
      rcases key with k | k | k | k | k
      · exact not_four_small_e M hns e he hd5 (by norm_num : 1 < 2) (by norm_num : 2 < 3)
          (by norm_num : 3 < 4) (by norm_num : 4 < 5) k
      · exact not_four_small_e M hns e he hd5 (by norm_num : 0 < 2) (by norm_num : 2 < 3)
          (by norm_num : 3 < 4) (by norm_num : 4 < 5) k
      · exact not_four_small_e M hns e he hd5 (by norm_num : 0 < 1) (by norm_num : 1 < 3)
          (by norm_num : 3 < 4) (by norm_num : 4 < 5) k
      · exact not_four_small_e M hns e he hd5 (by norm_num : 0 < 1) (by norm_num : 1 < 2)
          (by norm_num : 2 < 4) (by norm_num : 4 < 5) k
      · exact not_four_small_e M hns e he hd5 (by norm_num : 0 < 1) (by norm_num : 1 < 2)
          (by norm_num : 2 < 3) (by norm_num : 3 < 5) k
    have hlocal := one_le_recv4 _ _ _ _ _ (decide (fLen M (e 0).symm = 3))
      (decide (fLen M (e 1).symm = 3)) (decide (fLen M (e 2).symm = 3))
      (decide (fLen M (e 3).symm = 3)) (decide (fLen M (e 4).symm = 3))
      (hδ _) (hδ _) (hδ _) (hδ _) (hδ _) hns'
    rw [h5]
    push_cast
    linarith
  · -- degrees six to ten
    rw [hsend0 (by omega), hrecv0 (by omega)]
    have : (6 : ℚ) ≤ G.degree v := by exact_mod_cast h610.1
    linarith
  · -- an `11`-vertex
    rw [hrecv0 (by omega)]
    have h11q : (G.degree v : ℚ) = 11 := by exact_mod_cast h11
    rw [h11q] at hgle ⊢
    by_cases hz : ∃ d ∈ F, g4 M d = 0
    · obtain ⟨d, hd, hd0⟩ := hz
      have h1 := Finset.add_sum_erase F (g4 M) hd
      have h2 : ∑ x ∈ F.erase d, g4 M x ≤ (F.erase d).card • (1 / 2 : ℚ) :=
        Finset.sum_le_card_nsmul _ _ _ (fun x _ => g4_le M x)
      rw [Finset.card_erase_of_mem hd, hFk, h11, nsmul_eq_mul] at h2
      norm_num at h2
      linarith
    by_cases hf : ∃ d ∈ F, bigF M d.symm = 1 / 2
    · obtain ⟨d, hd, hd2⟩ := hf
      have := Finset.single_le_sum (fun x _ => hbig0 x.symm) hd
      linarith
    exfalso
    push Not at hz hf
    have hmem : ∀ n, e n ∈ F := fun n => Finset.mem_filter.2 ⟨Finset.mem_univ _, hfst n⟩
    refine no_ring M hδ hns e hsucc (fun n => by rw [← h11]; exact hper n) (fun n => ?_)
      (fun n => ?_) (fun n => ?_)
    · have := hz (e n) (hmem n)
      unfold g4 at this
      by_contra hne
      exact this (if_neg hne)
    · have := hf (e n) (hmem n)
      have h3' := h3 n
      unfold bigF at this
      by_contra hne
      exact this (if_pos (by omega))
    · have := hz (e n) (hmem n)
      intro hx
      apply this
      unfold g4
      rw [hfst, h11]
      simp [hx]
  · -- degree at least twelve
    rw [hrecv0 (by omega)]
    have : (12 : ℚ) ≤ G.degree v := by exact_mod_cast h12
    linarith

/-! ### The light `4`-star -/

theorem exists_light_star4 [Nonempty V] (hG : IsPlanar G) (hδ : ∀ v, 5 ≤ G.degree v) :
    ¬ NoStar4 (G := G) := by
  intro hns
  obtain ⟨M⟩ := hG
  obtain ⟨v0⟩ := ‹Nonempty V›
  obtain ⟨u, hu⟩ : ∃ u, G.Adj v0 u := by
    have hpos : 0 < (G.neighborFinset v0).card := by
      rw [G.card_neighborFinset_eq_degree]
      have := hδ v0
      omega
    obtain ⟨u, hu⟩ := Finset.card_pos.1 hpos
    exact ⟨u, by simpa using hu⟩
  have hK : (1 : ℚ) ≤ numComponents M.rot (dartSymm G) := by
    exact_mod_cast one_le_numComponents M ⟨(v0, u), hu⟩
  have hsum := sum_charge M
  rw [sum_split4 M] at hsum
  have hV : 0 ≤ ∑ d : G.Dart, ((1 - 6 / (G.degree d.fst : ℚ)) + g4 M d.symm - g4 M d +
      bigF M d.symm) := by
    rw [← Finset.sum_fiberwise Finset.univ (fun d : G.Dart => d.fst)]
    exact Finset.sum_nonneg (fun v _ => vertex4_nonneg M hδ hns v)
  have hFc : 0 ≤ ∑ x : G.Dart, ((2 - 6 / (fLen M x : ℚ)) - bigF M x) := by
    rw [← sum_avg_cls (SameCycle.setoid M.facePerm)]
    exact Finset.sum_nonneg (fun x _ => div_nonneg (face_orbit_nonneg M hδ x) (Nat.cast_nonneg _))
  linarith

end LightStar4
