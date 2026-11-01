/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Lebesgue.Star4
public import Lebesgue.Path4Local

/-!
# Light `4`-paths in plane maps of minimum degree five

Let `M` be a plane map of a finite simple graph of minimum degree at least five without a path
on four vertices of weight at most `23` (`NoP4`). Move charge as follows:

* every face of length at least four gives `1/2` to each of its corners;
* a vertex of degree `7`, `8` or at least `9` sends `1/3`, `1/2` or `1/3` to each `5`-neighbour.

This replaces the rule of Jendrol' and Madaras (`(deg A - 6) / m(A)` from every vertex of degree
at least six, which relies on an edge-maximal counterexample being a triangulation) by fixed
amounts and face charges. `5`-vertices receive at least `1` (`LightPath4.one_le_recvP`). If two
consecutive `5`-neighbours of a vertex `A` of degree `7` or `8` span a triangle, every other
neighbour `W` gives the path `W A X Y` of weight at most `23` unless it is heavy, so `A` has only
those two `5`-neighbours; otherwise the corners between consecutive `5`-neighbours lie on faces
of length at least four and pay for them.
-/

@[expose] public section

namespace LightPath4

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Kotzig Borodin Lebesgue LightStar4

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- No path on four vertices has weight at most `23`. -/
def NoP4 : Prop :=
  ∀ a b c d : V, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → G.Adj a b → G.Adj b c →
    G.Adj c d → 24 ≤ G.degree a + G.degree b + G.degree c + G.degree d

variable (M : PlaneMap G)

/-- What the tail of `e` sends to its head. -/
noncomputable def gP (e : G.Dart) : ℚ := if G.degree e.snd = 5 then cQ (G.degree e.fst) else 0

theorem gP_nonneg (e : G.Dart) : 0 ≤ gP e := by
  unfold gP cQ
  split_ifs <;> norm_num

theorem sum_splitP :
    ∑ d : G.Dart, ((1 - 6 / (G.degree d.fst : ℚ)) + (2 - 6 / (fLen M d : ℚ))) =
      ∑ d : G.Dart, ((1 - 6 / (G.degree d.fst : ℚ)) + gP d.symm - gP d + bigF M d.symm) +
      ∑ x : G.Dart, ((2 - 6 / (fLen M x : ℚ)) - bigF M x) := by
  have h1 : ∑ d : G.Dart, gP d.symm = ∑ d : G.Dart, gP d :=
    Equiv.sum_comp (dartSymm G) gP
  have h2 : ∑ d : G.Dart, bigF M d.symm = ∑ d : G.Dart, bigF M d :=
    Equiv.sum_comp (dartSymm G) (bigF M)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [h1, h2]
  ring

/-- Consecutive darts `d`, `rot d` whose corner is on a triangle end at adjacent vertices. -/
theorem adj_of_tri {d : G.Dart} (h : fLen M d.symm = 3) : G.Adj (M.rot d).snd d.snd := by
  have h1 := (M.facePerm (M.facePerm d.symm)).adj
  rw [fst_facePerm, third_tri M h, ← rot_eq] at h1
  exact h1

theorem snd_ne_of_ne {d w : G.Dart} (hf : d.fst = w.fst) (hne : d ≠ w) : d.snd ≠ w.snd := by
  intro hs
  apply hne
  rw [SimpleGraph.Dart.ext_iff]
  exact Prod.ext hf hs

/-! ### Vertices -/

/-- A vertex of degree `7` or `8` stays nonnegative. -/
theorem sender78 (hδ : ∀ v, 5 ≤ G.degree v) (hnp : NoP4 (G := G)) (v : V)
    (hk : G.degree v = 7 ∨ G.degree v = 8)
    (hFk : (Finset.univ.filter (fun d : G.Dart => d.fst = v)).card = G.degree v)
    (hmemF : ∀ d ∈ Finset.univ.filter (fun d : G.Dart => d.fst = v), d.fst = v)
    (hbig0 : ∀ d : G.Dart, 0 ≤ bigF M d)
    (hsend : ∑ d ∈ Finset.univ.filter (fun d : G.Dart => d.fst = v), gP d =
      (((Finset.univ.filter (fun d : G.Dart => d.fst = v)).filter
        (fun d => G.degree d.snd = 5)).card : ℚ) * cQ (G.degree v))
    (hrecv : ∑ d ∈ Finset.univ.filter (fun d : G.Dart => d.fst = v), gP d.symm = 0) :
    0 ≤ (G.degree v : ℚ) - 6 + ∑ d ∈ Finset.univ.filter (fun d : G.Dart => d.fst = v), gP d.symm -
      ∑ d ∈ Finset.univ.filter (fun d : G.Dart => d.fst = v), gP d +
      ∑ d ∈ Finset.univ.filter (fun d : G.Dart => d.fst = v), bigF M d.symm := by
  have hδ2 : ∀ v, 2 ≤ G.degree v := fun v => by have := hδ v; omega
  set F := Finset.univ.filter (fun d : G.Dart => d.fst = v) with hF
  set S := F.filter (fun d => G.degree d.snd = 5) with hSdef
  rw [hrecv, hsend]
  have hrotF : ∀ d ∈ F, M.rot d ∈ F := fun d hd =>
    Finset.mem_filter.2 ⟨Finset.mem_univ _, (M.isRotationSystem.fst_apply d).trans (hmemF d hd)⟩
  have hcount := card_add_card_le M.rot hrotF
    (Finset.filter_subset (fun d : G.Dart => G.degree d.snd = 5) F)
  rw [← hSdef, hFk] at hcount
  have hc : cQ (G.degree v) = if G.degree v = 7 then 1 / 3 else 1 / 2 := by
    unfold cQ
    rcases hk with h | h <;> simp [h]
  by_cases htri : ∃ d ∈ S.filter (fun d => M.rot d ∈ S), fLen M d.symm = 3
  · obtain ⟨d, hd, ht⟩ := htri
    have hd' := Finset.mem_filter.1 hd
    have hd1 := Finset.mem_filter.1 hd'.1
    have hd2 := Finset.mem_filter.1 hd'.2
    have hdv : d.fst = v := hmemF d hd1.1
    have hrdv : (M.rot d).fst = v := (M.isRotationSystem.fst_apply d).trans hdv
    have hXY : G.Adj (M.rot d).snd d.snd := adj_of_tri M ht
    have hsub : S ⊆ {d, M.rot d} := by
      intro w hw
      have hw1 := Finset.mem_filter.1 hw
      have hwv : w.fst = v := hmemF w hw1.1
      by_contra hnot
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
      have hWv : G.Adj w.snd v := by
        have := w.adj
        rw [hwv] at this
        exact this.symm
      have hvX : G.Adj v d.snd := by
        have := d.adj
        rwa [hdv] at this
      have := hnp w.snd v d.snd (M.rot d).snd hWv.ne
        (snd_ne_of_ne (hwv.trans hdv.symm) hnot.1)
        (snd_ne_of_ne (hwv.trans hrdv.symm) hnot.2) hvX.ne
        (by have := (M.rot d).adj; rw [hrdv] at this; exact this.ne) hXY.ne.symm
        hWv hvX hXY.symm
      rw [hw1.2, hd1.2, hd2.2] at this
      rcases hk with h | h <;> omega
    have hS2 : (S.card : ℚ) ≤ 2 := by
      have := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
      exact_mod_cast this
    have hB : 0 ≤ ∑ d ∈ F, bigF M d.symm := Finset.sum_nonneg (fun d _ => hbig0 _)
    rcases hk with h | h
    · rw [show cQ (G.degree v) = 1 / 3 by rw [h]; norm_num [cQ], h]
      push_cast
      linarith
    · rw [show cQ (G.degree v) = 1 / 2 by rw [h]; norm_num [cQ], h]
      push_cast
      linarith
  · push Not at htri
    have hbigS : ∀ d ∈ S.filter (fun d => M.rot d ∈ S), bigF M d.symm = 1 / 2 := by
      intro d hd
      have h3 := three_le_fLen M hδ2 d.symm
      unfold bigF
      rw [if_pos (by have := htri d hd; omega)]
    have hB : ((S.filter (fun d => M.rot d ∈ S)).card : ℚ) / 2 ≤ ∑ d ∈ F, bigF M d.symm := by
      have hsub : S.filter (fun d => M.rot d ∈ S) ⊆ F :=
        (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
      calc ((S.filter (fun d => M.rot d ∈ S)).card : ℚ) / 2
          = ∑ d ∈ S.filter (fun d => M.rot d ∈ S), bigF M d.symm := by
            rw [Finset.sum_congr rfl hbigS, Finset.sum_const, nsmul_eq_mul]
            ring
        _ ≤ ∑ d ∈ F, bigF M d.symm :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => hbig0 _)
    have hc' : ((S.card + S.card : ℕ) : ℚ) ≤ ((G.degree v + (S.filter (fun d => M.rot d ∈ S)).card : ℕ) : ℚ) := by
      exact_mod_cast hcount
    push_cast at hc'
    have hP0 : (0 : ℚ) ≤ ((S.filter (fun d => M.rot d ∈ S)).card : ℚ) := Nat.cast_nonneg _
    rcases hk with h | h
    · rw [show cQ (G.degree v) = 1 / 3 by rw [h]; norm_num [cQ]]
      rw [h] at hc' ⊢
      push_cast at hc' ⊢
      rcases Nat.lt_or_ge S.card 4 with hs | hs
      · have : (S.card : ℚ) ≤ 3 := by exact_mod_cast (by omega : S.card ≤ 3)
        linarith
      · have : (4 : ℚ) ≤ S.card := by exact_mod_cast hs
        linarith
    · rw [show cQ (G.degree v) = 1 / 2 by rw [h]; norm_num [cQ]]
      rw [h] at hc' ⊢
      push_cast at hc' ⊢
      linarith

theorem vertexP_nonneg (hδ : ∀ v, 5 ≤ G.degree v) (hnp : NoP4 (G := G)) (v : V) :
    0 ≤ ∑ d ∈ Finset.univ.filter (fun d : G.Dart => d.fst = v),
      ((1 - 6 / (G.degree d.fst : ℚ)) + gP d.symm - gP d + bigF M d.symm) := by
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
  have hrecv0 : G.degree v ≠ 5 → ∑ d ∈ F, gP d.symm = 0 := fun h =>
    Finset.sum_eq_zero (fun d hd => by
      unfold gP
      rw [show d.symm.snd = v from hmemF d hd, if_neg h])
  have hsend : ∑ d ∈ F, gP d = ((F.filter (fun d => G.degree d.snd = 5)).card : ℚ) *
      cQ (G.degree v) := by
    rw [Finset.card_filter]
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    unfold gP
    rw [hmemF d hd]
    split_ifs <;> simp
  rcases (show G.degree v = 5 ∨ G.degree v = 6 ∨ G.degree v = 7 ∨ G.degree v = 8 ∨
      9 ≤ G.degree v by omega) with h5 | h6 | h78 | h78 | h9
  · -- a `5`-vertex receives at least `1`
    rw [hsend, h5, show cQ 5 = 0 by simp [cQ], mul_zero]
    obtain ⟨e, hsucc, hper0, hfst, hinj, himg⟩ := enum M v (by omega)
    have hsumF : ∀ f : G.Dart → ℚ, ∑ d ∈ F, f d = ∑ n ∈ Finset.range (G.degree v), f (e n) :=
      fun f => by rw [show F = _ from himg.symm, Finset.sum_image hinj]
    have hper : ∀ n, e (n + 5) = e n := by
      intro n
      induction n with
      | zero => rw [← h5]; simpa using hper0
      | succ n ih => rw [show n + 1 + 5 = (n + 5) + 1 by ring, hsucc, ih, hsucc]
    have hrot : ∀ n m, (M.rot ^ m) (e n) = e (n + m) := by
      intro n m
      induction m with
      | zero => simp
      | succ m ih => rw [pow_succ', Perm.mul_apply, ih, ← add_assoc, hsucc]
    have h3 : ∀ n, 3 ≤ fLen M (e n).symm := fun n => three_le_fLen M hδ2 _
    have hd5 : ∀ n, G.degree (e n).fst = 5 := fun n => by rw [hfst, h5]
    -- the triangle conditions
    have hfact : ∀ i j, 2 ≤ j → j ≤ 4 → fLen M (e i).symm = 3 →
        19 ≤ G.degree (e (i + j)).snd + G.degree (e i).snd + G.degree (e (i + 1)).snd := by
      intro i j hj2 hj4 ht
      have hadj := adj_of_tri M ht
      rw [← hsucc] at hadj
      have hX : ∀ m, G.Adj v (e m).snd := fun m => by
        have := (e m).adj
        rwa [hfst] at this
      have hne : ∀ a b, a < b → b < 5 → (e (i + a)).snd ≠ (e (i + b)).snd := by
        intro a b hab hb
        have := rot_pow_snd_ne M (hd5 i) hab hb
        rwa [hrot, hrot] at this
      have hv : ∀ m, v ≠ (e m).snd := fun m => (hX m).ne
      have := hnp (e (i + j)).snd v (e i).snd (e (i + 1)).snd (hv _).symm
        (by have := hne 0 j (by omega) (by omega); rw [add_zero] at this; exact this.symm)
        (hne 1 j (by omega) (by omega)).symm (hv _) (hv _)
        (by have := hne 0 1 (by omega) (by omega); rwa [add_zero] at this)
        (hX _).symm (hX _) hadj.symm
      rw [h5] at this
      omega
    have hval : ∀ n, gP (e n).symm + bigF M (e n).symm =
        cQ (G.degree (e n).snd) + fQ (decide (fLen M (e n).symm = 3)) := by
      intro n
      have hX : G.degree (e n).symm.snd = 5 := by
        change G.degree (e n).fst = 5
        exact hd5 n
      unfold gP
      rw [if_pos hX]
      congr 1
      unfold bigF fQ
      by_cases ht : fLen M (e n).symm = 3
      · simp [ht]
      · have := h3 n
        simp [ht, show 4 ≤ fLen M (e n).symm by omega]
    have hsum : ∑ d ∈ F, gP d.symm + ∑ d ∈ F, bigF M d.symm =
        ∑ n ∈ Finset.range 5, (cQ (G.degree (e n).snd) + fQ (decide (fLen M (e n).symm = 3))) := by
      rw [← Finset.sum_add_distrib, hsumF, h5]
      exact Finset.sum_congr rfl (fun n _ => hval n)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hsum
    have hok : okP (cap9 (G.degree (e 0).snd)) (cap9 (G.degree (e 1).snd))
        (cap9 (G.degree (e 2).snd)) (cap9 (G.degree (e 3).snd)) (cap9 (G.degree (e 4).snd))
        (decide (fLen M (e 0).symm = 3)) (decide (fLen M (e 1).symm = 3))
        (decide (fLen M (e 2).symm = 3)) (decide (fLen M (e 3).symm = 3))
        (decide (fLen M (e 4).symm = 3)) = true := by
      have k : ∀ i j, 2 ≤ j → j ≤ 4 → fLen M (e i).symm = 3 →
          okC (cap9 (G.degree (e (i + j)).snd)) (cap9 (G.degree (e i).snd))
            (cap9 (G.degree (e (i + 1)).snd)) = true := fun i j h1 h2 ht =>
        okC_cap (hδ _) (hδ _) (hδ _) (hfact i j h1 h2 ht)
      have p : ∀ n, e (n + 5) = e n := hper
      have cc : ∀ i, ¬ fLen M (e i).symm = 3 ∨
          ((okC (cap9 (G.degree (e (i + 2)).snd)) (cap9 (G.degree (e i).snd))
            (cap9 (G.degree (e (i + 1)).snd)) = true ∧
          okC (cap9 (G.degree (e (i + 3)).snd)) (cap9 (G.degree (e i).snd))
            (cap9 (G.degree (e (i + 1)).snd)) = true) ∧
          okC (cap9 (G.degree (e (i + 4)).snd)) (cap9 (G.degree (e i).snd))
            (cap9 (G.degree (e (i + 1)).snd)) = true) := by
        intro i
        by_cases ht : fLen M (e i).symm = 3
        · exact Or.inr ⟨⟨k i 2 le_rfl (by norm_num) ht, k i 3 (by norm_num) (by norm_num) ht⟩,
            k i 4 (by norm_num) le_rfl ht⟩
        · exact Or.inl ht
      have c0 := cc 0
      have c1 := cc 1
      have c2 := cc 2
      have c3 := cc 3
      have c4 := cc 4
      rw [show (1 : ℕ) + 4 = 0 + 5 from rfl, p 0] at c1
      rw [show (2 : ℕ) + 3 = 0 + 5 from rfl, p 0, show (2 : ℕ) + 4 = 1 + 5 from rfl, p 1] at c2
      rw [show (3 : ℕ) + 2 = 0 + 5 from rfl, p 0, show (3 : ℕ) + 3 = 1 + 5 from rfl, p 1,
        show (3 : ℕ) + 4 = 2 + 5 from rfl, p 2] at c3
      rw [show (4 : ℕ) + 1 = 0 + 5 from rfl, p 0, show (4 : ℕ) + 2 = 1 + 5 from rfl, p 1,
        show (4 : ℕ) + 3 = 2 + 5 from rfl, p 2, show (4 : ℕ) + 4 = 3 + 5 from rfl, p 3] at c4
      simp only [okP, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
        decide_eq_false_iff_not]
      exact ⟨⟨⟨⟨c0, c1⟩, c2⟩, c3⟩, c4⟩
    have hlocal := one_le_recvP _ _ _ _ _ _ _ _ _ _ (hδ _) (hδ _) (hδ _) (hδ _) (hδ _) hok
    push_cast
    linarith
  · -- a `6`-vertex
    rw [hsend, hrecv0 (by omega), h6, show cQ 6 = 0 by simp [cQ], mul_zero]
    push_cast
    linarith
  · exact sender78 M hδ hnp v (Or.inl h78) hFk hmemF hbig0 hsend (hrecv0 (by omega))
  · exact sender78 M hδ hnp v (Or.inr h78) hFk hmemF hbig0 hsend (hrecv0 (by omega))
  · -- degree at least nine
    rw [hsend, hrecv0 (by omega), show cQ (G.degree v) = 1 / 3 by
      unfold cQ; rw [if_neg (by omega), if_neg (by omega), if_pos h9]]
    have hS : ((F.filter (fun d => G.degree d.snd = 5)).card : ℚ) ≤ G.degree v := by
      rw [← hFk]
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ F)
    have : (9 : ℚ) ≤ G.degree v := by exact_mod_cast h9
    linarith

/-! ### The light `4`-path -/

theorem exists_light_path4 [Nonempty V] (hG : IsPlanar G) (hδ : ∀ v, 5 ≤ G.degree v) :
    ¬ NoP4 (G := G) := by
  intro hnp
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
  rw [sum_splitP M] at hsum
  have hV : 0 ≤ ∑ d : G.Dart, ((1 - 6 / (G.degree d.fst : ℚ)) + gP d.symm - gP d +
      bigF M d.symm) := by
    rw [← Finset.sum_fiberwise Finset.univ (fun d : G.Dart => d.fst)]
    exact Finset.sum_nonneg (fun v _ => vertexP_nonneg M hδ hnp v)
  have hFc : 0 ≤ ∑ x : G.Dart, ((2 - 6 / (fLen M x : ℚ)) - bigF M x) := by
    rw [← sum_avg_cls (SameCycle.setoid M.facePerm)]
    exact Finset.sum_nonneg (fun x _ => div_nonneg (face_orbit_nonneg M hδ x) (Nat.cast_nonneg _))
  linarith

end LightPath4
