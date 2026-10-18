/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import MengerHamilton.ChvatalErdosAux

/-!
# Dirac's theorem: `k` vertices of a `k`-connected graph lie on a common cycle

A finite graph `G` is `k`-connected if it has more than `k` vertices and stays connected after
deleting any set of fewer than `k` vertices (`(G.induce Sᶜ).Connected` for `S.ncard < k`).

* `DiracCycle.exists_cycle_through`: **Dirac (1960).** In a `k`-connected finite graph with
  `k ≥ 2`, any set of at most `k` vertices lies on a common cycle (Mathlib's
  `SimpleGraph.Walk.IsCycle`).
* `DiracCycle.exists_cycle_through_pair`: in particular, in a `2`-connected finite graph any two
  vertices lie on a common cycle.
-/

@[expose] public section

open Finset SimpleGraph

namespace DiracCycle

section Aux

open Hamiltonicity

variable {V : Type*} {G : SimpleGraph V}

/-- Splice: replace the cyclic arc from `f 0` to `f d` by a path `Q` whose interior is off the
cycle. The new cycle contains `Q` and the arc `f d, …, f m`. -/
lemma splice {m : ℕ} {f : ℕ → V} (hC : CycArr G m f) {d : ℕ} (hd1 : 1 ≤ d) (hdm : d < m)
    (Q : G.Walk (f 0) (f d)) (hQ : Q.IsPath) (hQl : 2 ≤ Q.length)
    (hint : ∀ y ∈ Q.support, ∀ i, f i = y → y = f 0 ∨ y = f d) :
    ∃ m' g, CycArr G m' g ∧ (∀ y ∈ Q.support, ∃ i, g i = y) ∧
      ∀ i, d ≤ i → i ≤ m → ∃ j, g j = f i := by
  set l := Q.length with hl
  have hm := hC.three_le
  set q := Q.getVert with hq
  have hq0 : q 0 = f 0 := Q.getVert_zero
  have hql : q l = f d := Q.getVert_length
  have hqinj : ∀ i j, i ≤ l → j ≤ l → q i = q j → i = j := fun i j hi hj h =>
    hQ.getVert_injOn (by simp only [Set.mem_ofPred_eq]; omega)
      (by simp only [Set.mem_ofPred_eq]; omega) h
  have hqoff : ∀ i, 0 < i → i < l → ∀ j, f j ≠ q i := by
    intro i hi0 hil j hj
    rcases hint (q i) (Q.getVert_mem_support i) j hj with h | h
    · have := hqinj i 0 (by omega) (by omega) (h.trans hq0.symm)
      omega
    · have := hqinj i l (by omega) le_rfl (h.trans hql.symm)
      omega
  have hfinj : ∀ i j, i < m → j < m → f i = f j → i = j := hC.inj
  set h : ℕ → V := fun j => if j ≤ l then q j else f (j - l + d) with hh
  have hA : ∀ j, j ≤ l → h j = q j := fun j hj => by
    simp only [hh]
    rw [ite_eq_left hj]
  have hB : ∀ j, l < j → h j = f (j - l + d) := fun j hj => by
    simp only [hh]
    rw [ite_eq_right (by omega)]
  have hend : h (l + (m - d)) = h 0 := by
    rw [hB _ (by omega), hA 0 (Nat.zero_le _), hq0,
      show l + (m - d) - l + d = 0 + m by omega, hC.periodic]
  have hCA := CycArr.of_fun (G := G) (m := l + (m - d)) (h := h) (by omega) ?_ ?_ hend
  · refine ⟨_, _, hCA, ?_, ?_⟩
    · intro y hy
      obtain ⟨n, hn, hnl⟩ := Walk.mem_support_iff_exists_getVert.1 hy
      refine ⟨n, ?_⟩
      rw [Nat.mod_eq_of_lt (by omega), hA n hnl]
      exact hn
    · intro i hi1 hi2
      by_cases him : i = m
      · subst him
        refine ⟨0, ?_⟩
        rw [Nat.zero_mod]
        rw [hA 0 (Nat.zero_le _), hq0, show i = 0 + i by omega, hC.periodic]
      by_cases hid : i = d
      · subst hid
        refine ⟨l, ?_⟩
        rw [Nat.mod_eq_of_lt (by omega), hA l le_rfl, hql]
      · refine ⟨i - d + l, ?_⟩
        rw [Nat.mod_eq_of_lt (by omega), hB _ (by omega), show i - d + l - l + d = i by omega]
  · intro a b ha hb hab
    have hmix : ∀ a b, a ≤ l → l < b → b < l + (m - d) → h a ≠ h b := by
      intro a b ha hb1 hb2 hab
      rw [hA a ha, hB b hb1] at hab
      by_cases ha0 : a = 0
      · subst ha0
        rw [hq0] at hab
        have := hfinj _ _ (by omega) (by omega) hab
        omega
      by_cases hal : a = l
      · subst hal
        rw [hql] at hab
        have := hfinj _ _ (by omega) (by omega) hab
        omega
      exact hqoff a (by omega) (by omega) _ hab.symm
    by_cases ha' : a ≤ l <;> by_cases hb' : b ≤ l
    · rw [hA a ha', hA b hb'] at hab
      exact hqinj a b ha' hb' hab
    · exact absurd hab (hmix a b ha' (by omega) hb)
    · exact absurd hab.symm (hmix b a hb' (by omega) ha)
    · rw [hB a (by omega), hB b (by omega)] at hab
      have := hfinj _ _ (by omega) (by omega) hab
      omega
  · intro j hj
    rcases lt_trichotomy j l with hjl | rfl | hjl
    · rw [hA j hjl.le, hA (j + 1) hjl]
      exact Q.adj_getVert_succ hjl
    · rw [hA _ le_rfl, hql, hB _ (by omega), show Q.length + 1 - Q.length + d = d + 1 by omega]
      exact hC.adj d
    · rw [hB j hjl, hB (j + 1) (by omega), show j + 1 - l + d = j - l + d + 1 by omega]
      exact hC.adj _

/-- Two paths from `x` sharing only `x` give a path between their ends. -/
lemma isPath_reverse_append {x u v : V} (P₁ : G.Walk x u) (P₂ : G.Walk x v) (h₁ : P₁.IsPath)
    (h₂ : P₂.IsPath) (hdisj : ∀ y ∈ P₁.support, y ∈ P₂.support → y = x) :
    (P₁.reverse.append P₂).IsPath := by
  rw [Walk.isPath_def, Walk.support_append, Walk.support_reverse, List.nodup_append]
  refine ⟨List.nodup_reverse.2 h₁.support_nodup, h₂.support_nodup.sublist (List.tail_sublist _),
    ?_⟩
  intro a ha b hb hab
  subst hab
  rw [List.mem_reverse] at ha
  have hax := hdisj a ha (List.mem_of_mem_tail hb)
  subst hax
  have hn := h₂.support_nodup
  rw [← Walk.cons_tail_support, List.nodup_cons] at hn
  exact hn.1 hb

/-- The final splicing step: two paths from an off-cycle vertex `x` to `f a` and `f b`
(`a < b < m`) give a cycle through `x` and through all `f p` with `p = 0`, `p ≤ a` or `b ≤ p`. -/
lemma splice_two {m : ℕ} {f : ℕ → V} (hC : CycArr G m f) {x : V} (hx : ∀ i, f i ≠ x)
    {a b : ℕ} (hab : a < b) (hbm : b < m) (P₁ : G.Walk x (f a)) (P₂ : G.Walk x (f b))
    (h₁ : P₁.IsPath) (h₂ : P₂.IsPath)
    (hC₁ : ∀ y ∈ P₁.support, ∀ i, f i = y → y = f a)
    (hC₂ : ∀ y ∈ P₂.support, ∀ i, f i = y → y = f b)
    (hdisj : ∀ y ∈ P₁.support, y ∈ P₂.support → y = x) :
    ∃ m' g, CycArr G m' g ∧ (∃ i, g i = x) ∧
      ∀ p < m, (p = 0 ∨ p ≤ a ∨ b ≤ p) → ∃ i, g i = f p := by
  have hR := hC.rotate a
  have hl₁ : 1 ≤ P₁.length := by
    rcases Nat.eq_zero_or_pos P₁.length with h | h
    · exact absurd (Walk.eq_of_length_eq_zero h).symm (hx a)
    · exact h
  have hl₂ : 1 ≤ P₂.length := by
    rcases Nat.eq_zero_or_pos P₂.length with h | h
    · exact absurd (Walk.eq_of_length_eq_zero h).symm (hx b)
    · exact h
  have e₀ : f a = f (a + 0) := rfl
  have e₁ : f b = f (a + (b - a)) := by rw [show a + (b - a) = b by omega]
  set Q := (P₁.reverse.append P₂).copy e₀ e₁ with hQ
  have hQs : ∀ y, y ∈ Q.support ↔ y ∈ P₁.support ∨ y ∈ P₂.support := by
    intro y
    rw [hQ, Walk.support_copy, Walk.mem_support_append_iff, Walk.support_reverse,
      List.mem_reverse]
  obtain ⟨m', g, hg, hgQ, hgarc⟩ := splice hR (d := b - a) (by omega) (by omega) Q
    (by rw [hQ, Walk.isPath_copy]; exact isPath_reverse_append P₁ P₂ h₁ h₂ hdisj)
    (by rw [hQ, Walk.length_copy, Walk.length_append, Walk.length_reverse]; omega)
    (by
      intro y hy i hi
      rcases (hQs y).1 hy with hy | hy
      · exact Or.inl (hC₁ y hy (a + i) hi)
      · exact Or.inr ((hC₂ y hy (a + i) hi).trans e₁))
  refine ⟨m', g, hg, hgQ x ((hQs x).2 (Or.inl P₁.start_mem_support)), ?_⟩
  intro p hp hcase
  rcases hcase with h0 | hpa | hbp
  · obtain ⟨j, hj⟩ := hgarc (m - a) (by omega) (by omega)
    refine ⟨j, hj.trans ?_⟩
    rw [h0, show a + (m - a) = 0 + m by omega, hC.periodic]
  · obtain ⟨j, hj⟩ := hgarc (p + m - a) (by omega) (by omega)
    refine ⟨j, hj.trans ?_⟩
    rw [show a + (p + m - a) = p + m by omega, hC.periodic]
  · obtain ⟨j, hj⟩ := hgarc (p - a) (by omega) (by omega)
    refine ⟨j, hj.trans ?_⟩
    rw [show a + (p - a) = p by omega]

/-- Pigeonhole: if `R` has at least `#U + 2` elements, two elements of `R` have no element of `U`
strictly between them. -/
lemma exists_gap : ∀ (n : ℕ) (R U : Finset ℕ), #U = n → #U + 2 ≤ #R →
    ∃ a ∈ R, ∃ b ∈ R, a < b ∧ ∀ u ∈ U, ¬ (a < u ∧ u < b) := by
  intro n
  induction n with
  | zero =>
    intro R U hU hR
    rw [Finset.card_eq_zero] at hU
    subst hU
    obtain ⟨a, ha, b, hb, hab⟩ := (Finset.one_lt_card (s := R)).1 (by simp at hR; omega)
    rcases lt_or_gt_of_ne hab with h | h
    · exact ⟨a, ha, b, hb, h, by simp⟩
    · exact ⟨b, hb, a, ha, h, by simp⟩
  | succ n ih =>
    intro R U hU hR
    have hRne : R.Nonempty := Finset.card_pos.1 (by omega)
    set a := R.min' hRne with ha
    have hR'ne : (R.erase a).Nonempty :=
      Finset.card_pos.1 (by rw [Finset.card_erase_of_mem (R.min'_mem hRne)]; omega)
    set b := (R.erase a).min' hR'ne with hb
    have hbmem := (R.erase a).min'_mem hR'ne
    have hab : a < b := by
      rw [Finset.mem_erase] at hbmem
      exact lt_of_le_of_ne (R.min'_le _ hbmem.2) (Ne.symm hbmem.1)
    by_cases hgap : ∀ u ∈ U, ¬ (a < u ∧ u < b)
    · exact ⟨a, R.min'_mem hRne, b, Finset.mem_of_mem_erase hbmem, hab, hgap⟩
    push Not at hgap
    obtain ⟨u, hu, hau, hub⟩ := hgap
    obtain ⟨a', ha', b', hb', hab', hgap'⟩ := ih (R.erase a) (U.erase u)
      (by rw [Finset.card_erase_of_mem hu]; omega)
      (by rw [Finset.card_erase_of_mem hu, Finset.card_erase_of_mem (R.min'_mem hRne)]; omega)
    refine ⟨a', Finset.mem_of_mem_erase ha', b', Finset.mem_of_mem_erase hb', hab', ?_⟩
    intro w hw
    by_cases hwu : w = u
    · subst hwu
      have : b ≤ a' := (R.erase a).min'_le _ ha'
      omega
    · exact hgap' w (Finset.mem_erase.2 ⟨hwu, hw⟩)

/-- A cyclic arrangement gives a Mathlib cycle through all its vertices. -/
lemma exists_isCycle_support {m : ℕ} {f : ℕ → V} (h : CycArr G m f) :
    ∃ c : G.Walk (f 0) (f 0), c.IsCycle ∧ ∀ i, f i ∈ c.support := by
  have hm := h.three_le
  have hend : f (m - 1 + 1) = f 0 := by
    rw [show m - 1 + 1 = 0 + m by omega, h.periodic]
  let p := (walkOf G (fun i => f (i + 1)) (fun i => h.adj (i + 1)) (m - 1)).copy rfl hend
  refine ⟨Walk.cons (h.adj 0) p, ?_, ?_⟩
  · rw [Walk.cons_isCycle_iff]
    constructor
    · rw [Walk.isPath_def, Walk.support_copy, support_walkOf]
      refine List.Nodup.map_on ?_ List.nodup_range
      intro i hi j hj hij
      simp only [List.mem_range] at hi hj
      rw [h.eq_iff] at hij
      have := Nat.ModEq.add_right_cancel' 1 hij
      unfold Nat.ModEq at this
      rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    · rw [Walk.edges_copy, edges_walkOf]
      simp only [List.mem_map, List.mem_range, not_exists, not_and]
      intro i hi he
      rw [Sym2.eq_iff] at he
      rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have := h.inj _ _ (by omega) (by omega) h1
        omega
      · have := h.inj _ _ (by omega) (by omega) h1
        have h3 : i = 0 := by omega
        subst h3
        have := h.inj _ _ (by omega) (by omega) h2
        omega
  · intro i
    rw [h.eq_mod i, Walk.support_cons, List.mem_cons]
    have hlt : i % m < m := Nat.mod_lt _ h.pos
    by_cases h0 : i % m = 0
    · left; rw [h0]
    · right
      rw [Walk.support_copy, support_walkOf, List.mem_map]
      exact ⟨i % m - 1, List.mem_range.2 (by omega), by rw [show i % m - 1 + 1 = i % m by omega]⟩

/-- One induction step of Dirac's argument: a cycle containing `T` (with `f 0 ∈ T` if `T` is
nonempty) and a vertex `x` off it give a cycle containing `T` and `x`, provided `#T < k`. -/
lemma extend_through [Finite V] {k : ℕ} (hk : 2 ≤ k)
    (hconn : ∀ S : Set V, S.ncard < k → (G.induce Sᶜ).Connected)
    {m : ℕ} {f : ℕ → V} (hC : CycArr G m f) (T : Finset V) (hTk : #T < k)
    (hT0 : T.Nonempty → f 0 ∈ T) {x : V} (hx : ∀ i, f i ≠ x) :
    ∃ m' g, CycArr G m' g ∧ (∃ i, g i = x) ∧ ∀ p < m, f p ∈ T → ∃ i, g i = f p := by
  classical
  obtain ⟨r, hr, t, P, hP, hPC, hPd⟩ := exists_fan hconn hC hx
  have hm := hC.three_le
  have hm0 := hC.pos
  set s : Fin r → ℕ := fun j => t j % m with hs
  have hsinj : ∀ j j', s j = s j' → j = j' := by
    intro j j' hjj'
    by_contra hne
    have heq : f (t j) = f (t j') := hC.eq_iff.2 hjj'
    have h2 : f (t j) ∈ (P j').support := by rw [heq]; exact (P j').end_mem_support
    exact hx _ (hPd j j' hne (f (t j)) (P j).end_mem_support h2)
  have hsm : ∀ j, s j < m := fun j => Nat.mod_lt _ hm0
  obtain ⟨j₁, j₂, h12, hgood⟩ : ∃ j₁ j₂, s j₁ < s j₂ ∧
      ∀ p < m, f p ∈ T → p = 0 ∨ p ≤ s j₁ ∨ s j₂ ≤ p := by
    set R := Finset.univ.image s with hR
    have hRcard : #R = r := by
      rw [hR, Finset.card_image_of_injective _ (fun j j' h => hsinj j j' h), Finset.card_univ,
        Fintype.card_fin]
    by_cases hmk : m ≤ k
    · have hrm : m ≤ r := by rw [min_eq_right hmk] at hr; exact hr
      have hsub : R ⊆ Finset.range m := by
        intro y hy
        obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hy
        exact Finset.mem_range.2 (hsm j)
      have hReq : R = Finset.range m :=
        Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_range]; omega)
      obtain ⟨j₁, -, hj₁⟩ := Finset.mem_image.1 (hReq ▸ Finset.mem_range.2 (by omega) :
        (0 : ℕ) ∈ R)
      obtain ⟨j₂, -, hj₂⟩ := Finset.mem_image.1 (hReq ▸ Finset.mem_range.2 (by omega) :
        (1 : ℕ) ∈ R)
      refine ⟨j₁, j₂, by omega, fun p _ _ => by omega⟩
    · have hrk : k ≤ r := by rw [min_eq_left (by omega)] at hr; exact hr
      set U := (Finset.range m).filter (fun p => f p ∈ T ∧ p ≠ 0) with hU
      have hUcard : #U + 2 ≤ #R := by
        rw [hRcard]
        by_cases hTne : T.Nonempty
        · have h0 := hT0 hTne
          have hle : #U ≤ #(T.erase (f 0)) := by
            refine Finset.card_le_card_of_injOn f ?_ ?_
            · intro p hp
              rw [hU, Finset.coe_filter] at hp
              obtain ⟨hpm, hpT, hp0⟩ := hp
              refine Finset.mem_erase.2 ⟨fun h => hp0 ?_, hpT⟩
              exact hC.inj _ _ (Finset.mem_range.1 hpm) (by omega) h
            · intro p hp q hq hpq
              rw [hU, Finset.coe_filter] at hp hq
              exact hC.inj _ _ (Finset.mem_range.1 hp.1) (Finset.mem_range.1 hq.1) hpq
          rw [Finset.card_erase_of_mem h0] at hle
          have := Finset.card_pos.2 hTne
          omega
        · rw [Finset.not_nonempty_iff_eq_empty] at hTne
          subst hTne
          have : U = ∅ := by
            rw [hU]
            simp
          rw [this, Finset.card_empty]
          omega
      obtain ⟨a, ha, b, hb, hab, hgap⟩ := exists_gap _ R U rfl hUcard
      obtain ⟨j₁, -, rfl⟩ := Finset.mem_image.1 ha
      obtain ⟨j₂, -, rfl⟩ := Finset.mem_image.1 hb
      refine ⟨j₁, j₂, hab, fun p hp hpT => ?_⟩
      by_cases hp0 : p = 0
      · exact Or.inl hp0
      · have := hgap p (by rw [hU, Finset.mem_filter]; exact ⟨Finset.mem_range.2 hp, hpT, hp0⟩)
        omega
  have e : ∀ j, f (t j) = f (s j) := fun j => hC.eq_mod _
  obtain ⟨m', g, hg, hgx, hgarc⟩ := splice_two hC hx h12 (hsm j₂)
    ((P j₁).copy rfl (e j₁)) ((P j₂).copy rfl (e j₂))
    (by rw [Walk.isPath_copy]; exact hP j₁) (by rw [Walk.isPath_copy]; exact hP j₂)
    (by
      intro y hy i hi
      rw [Walk.support_copy] at hy
      exact (hPC j₁ y hy i hi).trans (e j₁))
    (by
      intro y hy i hi
      rw [Walk.support_copy] at hy
      exact (hPC j₂ y hy i hi).trans (e j₂))
    (by
      intro y hy₁ hy₂
      rw [Walk.support_copy] at hy₁ hy₂
      exact hPd j₁ j₂ (fun h => by rw [h] at h12; omega) y hy₁ hy₂)
  exact ⟨m', g, hg, hgx, fun p hp hpT => hgarc p hp (hgood p hp hpT)⟩

/-- Every set of at most `k` vertices lies on a common cyclic arrangement. -/
lemma exists_cycArr_through [Fintype V] {k : ℕ} (hk : 2 ≤ k) (hn : k < Fintype.card V)
    (hconn : ∀ S : Set V, S.ncard < k → (G.induce Sᶜ).Connected) (T : Finset V)
    (hT : #T ≤ k) : ∃ m f, CycArr G m f ∧ ∀ y ∈ T, ∃ i, f i = y := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    obtain ⟨m, f, h⟩ := exists_cycArr_of_conn (by omega) hk hconn
    exact ⟨m, f, h, by simp⟩
  | insert x T hxT ih =>
    rw [Finset.card_insert_of_notMem hxT] at hT
    obtain ⟨m, f, hC, hTC⟩ := ih (by omega)
    by_cases hxC : ∃ i, f i = x
    · refine ⟨m, f, hC, ?_⟩
      intro y hy
      rcases Finset.mem_insert.1 hy with rfl | hy
      · exact hxC
      · exact hTC y hy
    push Not at hxC
    -- rotate so that `f 0 ∈ T` when `T` is nonempty
    obtain ⟨f', hC', hTC', hx', hT0⟩ : ∃ f', CycArr G m f' ∧ (∀ y ∈ T, ∃ i, f' i = y) ∧
        (∀ i, f' i ≠ x) ∧ (T.Nonempty → f' 0 ∈ T) := by
      by_cases hTne : T.Nonempty
      · obtain ⟨y, hy⟩ := hTne
        obtain ⟨i, hi⟩ := hTC y hy
        refine ⟨fun j => f (i + j), hC.rotate i, ?_, fun j => hxC _, fun _ => by
          simp only [Nat.add_zero]; rw [hi]; exact hy⟩
        intro y' hy'
        obtain ⟨i', hi'⟩ := hTC y' hy'
        refine ⟨i' + m * i - i, ?_⟩
        have hm0 := hC.pos
        have : i ≤ i' + m * i := le_add_left (Nat.le_mul_of_pos_left i hm0)
        simp only
        rw [Nat.add_sub_cancel' this, hC.eq_mod, Nat.add_mul_mod_self_left, ← hC.eq_mod, hi']
      · exact ⟨f, hC, hTC, hxC, fun h => absurd h hTne⟩
    obtain ⟨m', g, hg, hgx, hgT⟩ := extend_through hk hconn hC' T (by omega) hT0 hx'
    refine ⟨m', g, hg, ?_⟩
    intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact hgx
    · obtain ⟨i, rfl⟩ := hTC' y hy
      rw [hC'.eq_mod i]
      exact hgT _ (Nat.mod_lt _ hC'.pos) (by rw [← hC'.eq_mod]; exact hy)

end Aux

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

/-- **Dirac's theorem (1960).** In a `k`-connected finite graph with `k ≥ 2`, any set `S` of at
most `k` vertices lies on a common cycle. -/
theorem exists_cycle_through {k : ℕ} (hk : 2 ≤ k) (hn : k < Fintype.card V)
    (hconn : ∀ S : Set V, S.ncard < k → (G.induce Sᶜ).Connected) (S : Finset V)
    (hS : #S ≤ k) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ ∀ x ∈ S, x ∈ c.support := by
  obtain ⟨m, f, hC, hSC⟩ := exists_cycArr_through hk hn hconn S hS
  obtain ⟨c, hc, hsup⟩ := exists_isCycle_support hC
  refine ⟨f 0, c, hc, fun x hx => ?_⟩
  obtain ⟨i, rfl⟩ := hSC x hx
  exact hsup i

/-- In a `2`-connected finite graph, any two vertices lie on a common cycle. -/
theorem exists_cycle_through_pair (hn : 2 < Fintype.card V)
    (hconn : ∀ S : Set V, S.ncard < 2 → (G.induce Sᶜ).Connected) (a b : V) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ a ∈ c.support ∧ b ∈ c.support := by
  classical
  obtain ⟨v, c, hc, hab⟩ := exists_cycle_through G le_rfl hn hconn {a, b} Finset.card_le_two
  exact ⟨v, c, hc, hab a (by simp), hab b (by simp)⟩

end DiracCycle
