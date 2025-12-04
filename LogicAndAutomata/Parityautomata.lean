import LogicAndAutomata.NPA
import LogicAndAutomata.Stuttering

-- set_option pp.proofs true

namespace Automata
variable {A : Type}

theorem infOcc_comp_of_Finite {α β : Type*} {f : α → β}
    (hfin : Finite α) (xs : Stream' α) : InfOcc (f ∘ xs) = f '' InfOcc xs := by
  apply subset_antisymm
  · intro x hx
    obtain ⟨k, -, rfl⟩ := hx.exists
    simp only [InfOcc, Function.comp_apply, Set.mem_image, Set.mem_setOf_eq,
              Nat.frequently_atTop_iff_infinite] at hx ⊢
    have union : Set.iUnion (fun (x : α) ↦ { n | xs n = x ∧ (f x = f (xs k))}) =
      { n | (f ∘ xs) n = (f ∘ xs) k} := by aesop

    have notforallxfinite : ¬ (∀ (x: α), { n | xs n = x ∧ (f x = f (xs k))}.Finite) := by
      apply by_contradiction
      simp only [not_not]
      intro hfin
      have unionfin: (Set.iUnion (fun (x : α) ↦ { n | xs n = x ∧ (f x = f (xs k))})).Finite :=
        Set.finite_iUnion hfin
      rw [union] at unionfin
      exact hx unionfin

    simp only [not_forall] at notforallxfinite

    obtain ⟨x, hx⟩ := notforallxfinite
    use x
    let q := Nat.nth (fun n ↦ (xs n = x ∧ (f x = f (xs k)))) 0
    have qtrue : (xs q = x ∧ (f x = f (xs k))) := by
      simpa using (Nat.nth_mem_of_infinite hx 0)
    aesop
  · rw [Set.image_subset_iff]
    intro x hx
    simp only [InfOcc, Function.comp_apply, Set.preimage_setOf_eq, Set.mem_setOf,
               Filter.frequently_atTop] at hx ⊢
    intro a
    specialize hx a
    obtain ⟨b, ⟨hbge, hbomega⟩⟩ := hx
    use b
    apply congr_arg f at hbomega
    exact ⟨hbge, hbomega⟩

-- lemma infoccnomepty

-- Proof subset
-- Definitions
open scoped BigOperators in
open Classical in
/-- Definition 4.2.1  we use a recursive definition instead of the sum in the thesis. -/
noncomputable def subset_wb_f_pair {M : NPA A} (w : Stream' A) {ρ_w : Stream' (M.StutterClosed).State}
    -- (ρ_w_run : (M.StutterClosed).InfRun w ρ_w)
    (ρ_w_pareven : Even (sSup ((M.StutterClosed).parityMap '' InfOcc ρ_w))) : Stream' (A × ℕ)
| i =>
  -- let l := if i = 0 then 0 else (subset_wb_f_pair ρ_w_run ρ_w_pareven (i-1)).2
  -- let l := ∑ m ∈ Finset.range i, (subset_wb_f_pair ρ_w_run ρ_w_pareven m).2 + 1
  let l2 := ∑ m : Fin i, ((subset_wb_f_pair w ρ_w_pareven m).2 + 1)
  have notloopinletterstate : ∃ n>0, ¬(∃q, ρ_w (l2+n) = (q, Sum.inl (w l2))) := by
    expose_names
    apply Classical.by_contradiction
    intro h
    simp at h
    have infocceqone : InfOcc ((M.StutterClosed).parityMap ∘ ρ_w) = {1} := by
      unfold InfOcc
      have infoccnonemp : (InfOcc ((M.StutterClosed).parityMap ∘ ρ_w)).Nonempty := by
        rw [infOcc_comp_of_Finite (M.StutterClosed).FinState ρ_w]
        rw [Set.image_nonempty]
        have inf_event := @inf_occ_eventually (M.StutterClosed).State (M.StutterClosed).FinState ρ_w
        rw [Filter.eventually_atTop] at inf_event
        obtain ⟨k, hk⟩ := inf_event
        specialize hk k
        simp at hk
        exact Set.nonempty_of_mem hk
      unfold InfOcc at infoccnonemp

      rw [← Set.Nonempty.subset_singleton_iff infoccnonemp]
      rw [Set.subset_singleton_iff]
      apply Classical.by_contradiction

      simp only [Set.mem_setOf_eq, not_forall]
      intro h2
      obtain ⟨x, ⟨hx1, hx2⟩⟩ := h2
      rw [Filter.frequently_atTop] at hx1
      specialize hx1 (l2 + 1)
      obtain ⟨xge, ⟨hxge1, hxge2⟩⟩ := hx1
      specialize h (xge - l2)
      simp at h
      have hxgt : xge ≥ l2 := by omega
      apply Nat.lt_of_succ_le at hxge1
      apply h at hxge1
      obtain ⟨q, hxge⟩ := hxge1
      rw [Nat.add_sub_of_le hxgt] at hxge
      have parmapeqone : (M.StutterClosed).parityMap (ρ_w xge) = 1 := by
        rw [hxge]
        unfold NPA.parityMap
        unfold NPA.StutterClosed
        simp only [Sum.elim_inl]
      rw [← hxge2] at hx2
      exact hx2 parmapeqone

    rw [infOcc_comp_of_Finite (M.StutterClosed).FinState ρ_w] at infocceqone
    have ssupone : sSup ((M.StutterClosed).parityMap '' InfOcc ρ_w) = 1 := by
      simp only [infocceqone, csSup_singleton]

    have ssupodd : Odd (sSup ((M.StutterClosed).parityMap '' InfOcc ρ_w)) := by
      rw [ssupone]
      exact odd_one
    rw [← Nat.not_even_iff_odd] at ssupodd
    exact ssupodd ρ_w_pareven
  let k := Nat.find notloopinletterstate
  (w l2, k - 1)

noncomputable def subset_wb {M : NPA A} (w : Stream' A) {ρ_w : Stream' (M.StutterClosed).State}
    -- (ρ_w_run : (M.StutterClosed).InfRun w ρ_w)
    (ρ_w_pareven : Even (sSup ((M.StutterClosed).parityMap '' InfOcc ρ_w))) : Stream' A
| i => (subset_wb_f_pair w ρ_w_pareven i).1

noncomputable def subset_f {M : NPA A} (w : Stream' A) {ρ_w : Stream' (M.StutterClosed).State}
    -- (ρ_w_run : (M.StutterClosed).InfRun w ρ_w)
    (ρ_w_pareven : Even (sSup ((M.StutterClosed).parityMap '' InfOcc ρ_w))) : Stream' ℕ
| i => (subset_wb_f_pair w ρ_w_pareven i).2

-- ss is run op w
-- Definition 4.2.3
open Classical in
noncomputable def subset_f'_rhow'_pair {M : NPA A} {w : Stream' A} {f : Stream' ℕ}
                  {ρ_w : Stream' (M.StutterClosed).State} (ρ_w_run : (M.StutterClosed).InfRun w ρ_w)
                  (ρ_w_pareven : Even (sSup ((M.StutterClosed).parityMap '' InfOcc ρ_w)))
                  (hf : f = subset_f w ρ_w_pareven) : Stream' (ℕ × (Stream' M.State))

| i =>
  if hf : f i = 0 then
    let a := subset_wb w ρ_w_pareven i -- ((subset_wb_f_pair w ρ_w_pareven i).1)
    -- let s := ∑ m : Fin i, ((subset_f w ρ_w_pareven m) + 1)
    -- let e := ∑ m : Fin i, ((subset_f w ρ_w_pareven m) + 1) + (f i + 1)
    let s := ∑ m : Fin i, (f m + 1)
    let e := ∑ m : Fin i, (f m + 1) + (f i + 1)
    -- ∑ m : Fin (i+1), ((subset_wb_f_pair w ρ_w_pareven m).2 + 1)
    have this : ∃ n, ∃ ρ : Stream' M.State,
                (M.FinRunStart n (fun _ ↦ a) ρ (ρ_w s).1
                ∧ (Sum.inr (sSup (M.parityMap '' (ρ '' {l| (l > 0) ∧ (l ≤ n)}))) = (ρ_w e).2)
                ∧ ρ n = (ρ_w e).1) := by
      obtain ⟨ρ_w_init, ρ_w_next⟩ := ρ_w_run
      specialize ρ_w_next s
      have hs : s = ∑ m : Fin i, (f m + 1) := by trivial
      have he : e = ∑ m : Fin i, (f m + 1) + (f i + 1) := by trivial
      rw [hf] at he
      simp at he
      rw [he]
      rw [hs] at ρ_w_next
      rw [← he] at ρ_w_next
      unfold NA.next at ρ_w_next
      unfold NPA.StutterClosed at ρ_w_next
      simp at ρ_w_next
      -- Zeggen dat het een num state is want anders niet 0

      sorry
    -- Hier toevoegen dat max parity klpt
    -- Hier misschien de kleinste kiezen...
    -- let n := Nat.find ex
    ---...
    -- let n_h

    let n := this.choose
    let n_h := this.choose_spec
    let ss_fin :=  n_h.choose
    (n - 1, ss_fin)
    -- have dec: Decidable ((ss (subset_wb_f_pair hss heven (i+1)).2).1 ∈
    --           (M.next (ss (subset_wb_f_pair hss heven i).2).1 ((subset_wb_f_pair hss heven i).1)))
    --           := by sorry
    -- -- Finset.decidableMem
    -- if (ss (subset_wb_f_pair hss heven (i+1)).2).1 ∈
    --    (M.next (ss (subset_wb_f_pair hss heven i).2).1 ((subset_wb_f_pair hss heven i).1)) then
    --   (0, fun k ↦ if k = 1 then (ss (subset_wb_f_pair hss heven (k+1)).2).1 else (ss 0 ).1)
    -- else
    --   let a := ((subset_wb_f_pair hss heven i).1)
    --   have this : ∃n, ∃ ss' : Stream' M.State,
    --               (M.FinRunStart n (fun _ ↦ a) ss' (ss (subset_wb_f_pair hss heven i).2).1
    --               ∧ ss' n = (ss (subset_wb_f_pair hss heven (i+1)).2).1) := by sorry

    --   -- Hier misschien de kleinste kiezen...
    --   -- let n := Nat.find ex
    --   ---...
    --   -- let n_h

    --   let n := this.choose
    --   let n_h := this.choose_spec
    --   let ss_fin :=  n_h.choose
    --   (n, ss_fin)
  else
    (0, fun k↦ if k = 1 then (ρ_w (∑ m ∈ Finset.range (i + 1), (f m + 1))).1 else (ρ_w 0).1)

    -- (0, fun k↦ if k = 1 then (ρ_w (subset_wb_f_pair ρ_w_run ρ_w_pareven (i+1)).2).1 else (ρ_w 0).1)

noncomputable def subset_f' {M : NPA A} {w : Stream' A} {f : Stream' ℕ}
                  {ρ_w : Stream' (M.StutterClosed).State} (ρ_w_run : (M.StutterClosed).InfRun w ρ_w)
                  (ρ_w_pareven : Even (sSup ((M.StutterClosed).parityMap '' InfOcc ρ_w)))
                   (hf : f = subset_f w ρ_w_pareven) : Stream' ℕ
| i => (subset_f'_rhow'_pair ρ_w_run ρ_w_pareven hf i).1

noncomputable def subset_rhow' {M : NPA A} {w : Stream' A} {f : Stream' ℕ}
                  {ρ_w : Stream' (M.StutterClosed).State} (ρ_w_run : (M.StutterClosed).InfRun w ρ_w)
                  (ρ_w_pareven : Even (sSup ((M.StutterClosed).parityMap '' InfOcc ρ_w)))
                  (hf : f = subset_f w ρ_w_pareven) : Stream' M.State

| i =>
  let f' := subset_f' ρ_w_run ρ_w_pareven hf
  -- let i_b : ℕ :=  Nat.find (kexists (i) f')
  let i_b : ℕ :=  Nat.find (kexists (i - 1) f')
  let j := i - (∑ m ∈ Finset.range i_b, (f' m + 1))

  (subset_f'_rhow'_pair ρ_w_run ρ_w_pareven hf i_b).2 j
  -- (subset_f'_rhow'_pair ρ_w_run ρ_w_pareven f i).2 (i - (∑ m∈ Finset.range (Nat.find (kexists i (subset_f' ρ_w_run ρ_w_pareven f))), ((subset_f' ρ_w_run ρ_w_pareven f) m + 1)))

open Classical in
/-- Claim 4.2.2 (approximately) -/
lemma subset_stutequiv_w_w' {A : Type} {M : NPA A} {w : Stream' A} {f : Stream' ℕ}
        {ρ_w : Stream' (M.StutterClosed).State} (ρ_w_run : M.StutterClosed.InfRun w ρ_w)
        (ρ_w_pareven : Even (sSup ((M.StutterClosed).parityMap '' InfOcc ρ_w)))
        (hf : f = subset_f w ρ_w_pareven) :
        StutterEquivalent w (functiononword (subset_wb w ρ_w_pareven) (subset_f' ρ_w_run ρ_w_pareven hf)) := by
  unfold StutterEquivalent
  use (subset_wb w ρ_w_pareven)
  use f
  use (subset_f' ρ_w_run ρ_w_pareven hf)

  -- have ρ_w_run2 := ρ_w_run

  simp only [and_true]
  unfold functiononword
  apply funext

  intro x
  unfold subset_wb
  unfold subset_wb_f_pair
  simp only

  cases x
  case zero =>
    have hi_b : Nat.find (kexists 0 f) = 0 := by
      simp only [Nat.find_eq_zero, n_lt_sumk, zero_add, Finset.range_one, Finset.sum_singleton,
        lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true]
    rw [hi_b]
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
  case succ n =>
    if hi_b : (Nat.find (kexists (n+1) f)) = 0 then
      unfold subset_wb_f_pair
      simp only
      have hi_b2 := hi_b
      rw [Nat.find_eq_zero] at hi_b
      unfold n_lt_sumk at hi_b
      simp only [zero_add, Finset.range_one, Finset.sum_singleton] at hi_b
      rw [hf] at hi_b
      unfold subset_f at hi_b
      unfold subset_wb_f_pair at hi_b

      simp only [gt_iff_lt, Finset.univ_eq_empty, Finset.sum_empty, zero_add, not_exists,
        Nat.le_find_iff, Nat.lt_one_iff, not_and, not_forall, not_not, forall_eq, lt_self_iff_false,
        IsEmpty.forall_iff, Nat.sub_add_cancel, Nat.lt_find_iff] at hi_b
      rw [hi_b2]
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      specialize hi_b (n+1)
      simp at hi_b
      have ρ_w_next_spec : ρ_w (n+2) ∈ (M.StutterClosed).next (ρ_w (n + 1)) (w (n + 1)) :=
        ρ_w_run.2 (n+1)
      unfold NA.next at ρ_w_next_spec
      unfold NPA.toNA at ρ_w_next_spec
      unfold NPA.StutterClosed at ρ_w_next_spec

      obtain ⟨q, hq⟩ := hi_b
      rw [hq] at ρ_w_next_spec
      simp only [decide_eq_true_eq, gt_iff_lt, ge_iff_le, exists_and_left, exists_and_right,
        Set.mem_ite_empty_right, Set.mem_insert_iff, Set.mem_singleton_iff] at ρ_w_next_spec
      -- En hier staat precies het tweede gedeelte wat je wil hebben jippie :)
      apply Eq.symm (ρ_w_next_spec.1)
    else

      apply Nat.pos_of_ne_zero at hi_b
      rw [← Nat.add_one_le_iff] at hi_b

      have hi_b2 := hi_b
      apply Nat.le.dest at hi_b
      obtain ⟨k, hk⟩ := hi_b
      rw [← hk]
      have hk := hk.symm
      rename_i hk2
      clear hk2
      rw [Nat.find_eq_iff] at hk
      obtain ⟨k_spec, k_big⟩ := hk

      unfold n_lt_sumk at k_spec

      rw [Finset.sum_range_succ] at k_spec

      nth_rewrite 2 [hf] at k_spec

      unfold subset_f at k_spec
      unfold subset_wb_f_pair at k_spec

      simp only [gt_iff_lt, not_exists, Nat.le_find_iff, Nat.lt_one_iff, not_and, not_forall,
        not_not, forall_eq, lt_self_iff_false, add_zero, IsEmpty.forall_iff,
        Nat.sub_add_cancel] at k_spec


      unfold n_lt_sumk at k_big
      simp at k_big
      specialize k_big k
      simp at k_big

      have k_spec2 := k_spec
      rw [add_comm] at k_big
      rw [← Nat.sub_lt_iff_lt_add' k_big] at k_spec2
      apply Nat.le.dest at k_spec2
      obtain ⟨k2, hk2⟩ := k_spec2
      have hk3 := hk2.symm
      rw [Nat.find_eq_iff] at hk3
      obtain ⟨k2_spec, k2_big⟩ := hk3
      simp only [Nat.succ_eq_add_one, add_pos_iff, tsub_pos_iff_lt, zero_lt_one, or_true, true_or,
        true_and] at k2_spec
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, not_and, not_forall,
        Decidable.not_not] at k2_big
      simp only [hk2] at k2_big

      if heq: n+1 = ∑ m ∈ Finset.range (k+1), (f m + 1) then
        rw [heq]
        rw [zero_add, add_comm 1 k]
        rw [Fin.sum_univ_eq_sum_range (fun n ↦ ((subset_wb_f_pair w ρ_w_pareven n).2 + 1)) (k+1)]
        rw [hf]
        exact rfl
      else
        specialize k2_big (n+1 - ∑ m ∈ Finset.range (1+k), (f m + 1))
        rw [← Nat.sub_lt_iff_lt_add' k_big] at k_spec
        apply k2_big at k_spec
        rw [add_comm] at k_big
        rw [← ne_eq] at heq
        have hge : n+1 > ∑ m ∈ Finset.range (k+1), (f m + 1) :=
          Nat.lt_iff_le_and_ne.mpr ⟨k_big, heq.symm⟩

        apply GT.gt.lt at hge
        rw [← Nat.sub_lt_sub_iff_right (c:=∑ m ∈ Finset.range (k+1), (f m + 1)) (by simp)] at hge
        simp only [tsub_self] at hge
        rw [add_comm 1 k] at k_spec
        apply k_spec at hge
        obtain ⟨x, hx⟩ := hge
        rw [hf] at hx
        unfold subset_f at hx
        simp at hx
        nth_rewrite 1 [Fin.sum_univ_eq_sum_range (fun n ↦ ((subset_wb_f_pair w ρ_w_pareven n).2 + 1)) (k+1)] at hx
        have k_big2 := k_big
        rw [hf] at k_big2
        unfold subset_f at k_big2
        simp at k_big2
        rw [Nat.add_sub_cancel' k_big2] at hx
        have ρ_w_next_spec : ρ_w (n+2) ∈ (M.StutterClosed).next (ρ_w (n + 1)) (w (n + 1)) :=
          ρ_w_run.2 (n+1)
        unfold NA.next at ρ_w_next_spec
        unfold NPA.toNA at ρ_w_next_spec
        unfold NPA.StutterClosed at ρ_w_next_spec
        rw [hx] at ρ_w_next_spec
        simp at ρ_w_next_spec
        simp at k2_spec
        -- Hier weer tweede in de and gebruiken strakjes
        rw [zero_add, add_comm 1 k]
        apply Eq.symm (ρ_w_next_spec.1)


-- Claim 4.2.4
-- Deze is moeilijk met Malvin samen doen
lemma subset_rhow'_run {A : Type} {M : NPA A} {w wb: Stream' A} {f f' : Stream' ℕ} {ρ_w : Stream' (M.StutterClosed).State}
      (ρ_w_run : M.StutterClosed.InfRun w ρ_w)
      (ρ_w_pareven : Even (sSup ((M.StutterClosed).parityMap '' InfOcc ρ_w)))
      (hwb : wb = subset_wb w ρ_w_pareven)
      (hf : f = subset_f w ρ_w_pareven)
      (hf' : f' = subset_f' ρ_w_run ρ_w_pareven hf) :
      M.InfRun (functiononword wb f') (subset_rhow' ρ_w_run ρ_w_pareven hf) := by
  unfold NA.InfRun
  have ⟨ρ_w_init, ρ_w_next⟩ := ρ_w_run
  constructor
  · unfold subset_rhow'
    if hfzero : f 0 = 0 then
      unfold subset_f'_rhow'_pair

      -- simp [hf]
      -- simp! only [hf, ↓reduceIte, zero_tsub]

      dsimp only [↓reduceIte, zero_tsub, hf]
      sorry
      -- rw [hf]
      -- dsimp only [↓dreduceIte]

      -- simp only [zero_tsub]
      -- let a := wb 0
      -- let n := subset_f' w ρ_w_pareven f 0

      -- sorry
    else
      sorry
      -- hoe krijg je hier van alles uit die choose
    --   let ρ_p := (∃ ρ_p, (M.FinRunStart n (fun _ ↦ a) ρ_p (ρ_w 0).1
    --             ∧ ρ_p n = (ρ_w n).1)).choose
    --   have choose_spec : (M.FinRunStart n (fun _ ↦ a) ρ_p (ρ_w start).1
    --             ∧ ρ_p n = (ρ_w e).1) := by
    --   unfold subset_f'_rhow'_pair._proof_2
    --   unfold subset_f'_rhow'_pair._proof_1






    --   sorry
    -- else

    --   sorry

    -- sorry

    -- let i := 0
    -- let i_b := Nat.find (kexists i f')
    -- unfold kexists at i_b
    -- have zerotrue : (n_lt_sumk 0 f' 0) := by
    --   unfold n_lt_sumk
    --   simp only [zero_add, Finset.range_one, Finset.sum_singleton, lt_add_iff_pos_left, add_pos_iff,
    --     zero_lt_one, or_true]
    -- have i_b_zero : i_b = 0 := by
    --   apply (Nat.find_eq_zero (kexists i f')).2 zerotrue

    -- unfold i_b at i_b_zero

    -- unfold subset_f'_rhow'_pair
    -- simp only [↓reduceIte]
    -- simp only [zero_tsub]


    -- rw [i_b_zero]

    -- simp [zerotrue] at i_b

    -- simp at i_b

    -- simp only

    -- unfold NA.init NPA.toNA NPA.StutterClosed at ssinit
    -- simp only [decide_eq_true_eq, Set.mem_setOf_eq] at ssinit

    -- simp only [Set.mem_setOf_eq] at ssinit
    -- obtain ⟨s0, hs0⟩ := ssinit
    -- rw [← hs0.2]
    -- exact hs0.1
  · intro k

    unfold subset_rhow'
    unfold subset_f'_rhow'_pair
    simp only


    sorry

lemma infoccnonemp {A : Type} {M : NPA A} {ρ : Stream' M.State} : (InfOcc ρ).Nonempty := by
  unfold InfOcc
  rw [Set.nonempty_def]
  apply by_contradiction
  intro hneg
  apply forall_not_of_not_exists at hneg
  have forallxfinite : ∀ (x: M.State), (¬{ k:ℕ | ρ k = x}.Infinite) := by
    intro x
    have xnotinfilter : x∉ {x | ∃ᶠ (k : ℕ) in Filter.atTop, ρ k = x} := hneg x
    apply Set.notMem_setOf_iff.1 at xnotinfilter
    contrapose! xnotinfilter
    exact Nat.frequently_atTop_iff_infinite.2 xnotinfilter
  have union : Set.iUnion (fun (x : M.State)↦ { k:ℕ | ρ k = x}) = Set.univ := by
    rw [Set.iUnion_eq_univ_iff]
    intro k
    use ρ k
    simp only [Set.mem_setOf_eq]
  simp only [Set.not_infinite] at forallxfinite
  have unionfinite: (⋃ x, {k | ρ k = x}).Finite := @Set.finite_iUnion _ _ M.FinState _ forallxfinite
  rw [union] at unionfinite

  exact Set.infinite_univ unionfinite


lemma par_map_inf_occ_of_ss_has_sup {A : Type} (M : NPA A) (ss' : Stream' M.State) :
    ∃ n, ∀ a ∈ NPA.parityMap '' InfOcc ss', a ≤ n := by
  have htest : ∃ n∈ (InfOcc ss'), ∀ a ∈ (InfOcc ss'), (M.parityMap a) ≤ (M.parityMap n) := by
    apply Set.exists_max_image (InfOcc ss') (M.parityMap)
    · unfold InfOcc
      exact Set.Finite.subset (@Set.finite_univ M.State M.FinState) (fun ⦃a⦄ a ↦ trivial)
    · exact infoccnonemp
  obtain ⟨n, hn⟩:= htest
  use (M.parityMap n)
  intro a ha
  rw [Set.mem_image] at ha
  obtain ⟨xa, hxa⟩ := ha
  rw [← hxa.2]
  apply hn.2
  exact hxa.1

/- .-/
-- set_option pp.proofs true in
open Classical in
lemma sumpointseqnumstate  {M : NPA A} {w : Stream' A} {ρ_w : Stream' (M.StutterClosed).State} (f: Stream' ℕ)
    (ρ_w_run : M.StutterClosed.InfRun w ρ_w)
    (ρ_w_pareven : Even (sSup ((M.StutterClosed).parityMap '' InfOcc ρ_w)))
    (hf : f = subset_f w ρ_w_pareven) (i : ℕ) (hfi : f i > 0) :
    ∃ q, (ρ_w (∑ m ∈ Finset.range (i + 1), (f m + 1)) = (q, Sum.inr (⟨M.parityMap q, by simp⟩)))
    := by
  rw [hf]
  cases i
  case zero =>
    have hi_b : (Nat.find (kexists ((subset_f w ρ_w_pareven 0)) f)) = 0 := by
      rw [Nat.find_eq_zero]
      unfold n_lt_sumk
      rw [hf]
      simp only [zero_add, Finset.range_one, Finset.sum_singleton, lt_add_iff_pos_right,
        zero_lt_one]
    rw [Nat.find_eq_zero] at hi_b
    unfold n_lt_sumk at hi_b
    simp only [zero_add, Finset.range_one, Finset.sum_singleton] at hi_b
    rw [hf] at hi_b
    unfold subset_f at hi_b
    unfold subset_wb_f_pair at hi_b
    rw [hf] at hfi
    unfold subset_f at hfi
    unfold subset_wb_f_pair at hfi
    simp only at hfi
    simp only [gt_iff_lt, Finset.univ_eq_empty, Finset.sum_empty, zero_add,
      Nat.le_find_iff, Nat.lt_one_iff, not_and, not_not, forall_eq, lt_self_iff_false,
        IsEmpty.forall_iff, Nat.sub_add_cancel, Nat.lt_find_iff] at hi_b
    have ρ_w_next_spec : ρ_w (subset_f w ρ_w_pareven 0 + 1) ∈ (M.StutterClosed).next (ρ_w (subset_f w ρ_w_pareven 0)) (w (subset_f w ρ_w_pareven 0)) :=
        ρ_w_run.2 (subset_f w ρ_w_pareven 0)
    unfold NA.next at ρ_w_next_spec
    unfold NPA.toNA at ρ_w_next_spec
    unfold NPA.StutterClosed at ρ_w_next_spec
    unfold subset_f at ρ_w_next_spec
    unfold subset_wb_f_pair at ρ_w_next_spec
    simp at ρ_w_next_spec

    unfold subset_f
    unfold subset_wb_f_pair
    simp only

    specialize hi_b ((Nat.find (subset_wb_f_pair._proof_1 w ρ_w_pareven 0)) - 1)
    simp at hi_b
    simp at hfi
    apply hi_b at hfi
    obtain ⟨q, hq⟩ := hfi
    rw [hq] at ρ_w_next_spec
    simp at ρ_w_next_spec
    obtain ⟨_, ρ_w_sumstate⟩ := ρ_w_next_spec

    have this := (Nat.find_eq_iff (m:= Nat.find (subset_wb_f_pair._proof_1 w ρ_w_pareven 0)) ((subset_wb_f_pair._proof_1 w ρ_w_pareven 0)))
    simp at this
    simp
    use q
    obtain ⟨notloopstate, _⟩ := this
    specialize notloopstate q
    apply Or.resolve_left ρ_w_sumstate
    exact notloopstate
  case succ n =>
    simp only [add_assoc, Nat.reduceAdd]
    have k_spec : n_lt_sumk (∑ m ∈ Finset.range (n + 1), (f m + 1)) f (n+1) := by
      unfold n_lt_sumk
      nth_rewrite 2 [Finset.sum_range_succ]
      rw [add_comm]
      simp only [lt_add_iff_pos_right, add_pos_iff, zero_lt_one, or_true]
    unfold n_lt_sumk at k_spec
    nth_rewrite 2 [Finset.sum_range_succ] at k_spec

    have k_spec2 := k_spec
    nth_rewrite 3 [hf] at k_spec
    unfold subset_f at k_spec
    unfold subset_wb_f_pair at k_spec

    simp only  at k_spec
    rw [Nat.sub_add_cancel (by simp)] at k_spec
    rw [← Nat.sub_lt_iff_lt_add' (by simp)] at k_spec
    rw [Nat.sub_self] at k_spec
    apply Nat.le.dest at k_spec
    simp only [Nat.succ_eq_add_one, zero_add] at k_spec
    obtain ⟨k2, hk2⟩ := k_spec
    have hk2b := hk2.symm
    rw [Nat.find_eq_iff] at hk2b
    obtain ⟨k2_spec, k2_big⟩ := hk2b
    simp only [Nat.succ_eq_add_one, add_pos_iff, tsub_pos_iff_lt, zero_lt_one, or_true, true_or,
      true_and] at k2_spec
    simp only [hk2] at k2_big

    rw [hf] at hfi
    unfold subset_f at hfi
    unfold subset_wb_f_pair at hfi
    simp only at hfi

    specialize k2_big ((Nat.find (subset_wb_f_pair._proof_1 w ρ_w_pareven (n+1))) - 1)
    have le : (((Nat.find (subset_wb_f_pair._proof_1 w ρ_w_pareven (n+1))) - 1)) <
      (Nat.find (subset_wb_f_pair._proof_1 w ρ_w_pareven (n+1))) := by omega

    apply k2_big at le
    simp only [not_and] at le
    apply le at hfi
    simp only [not_not] at hfi
    obtain ⟨q, hq⟩ := hfi
    clear le
    clear k2_big

    have ρ_w_next_spec : ρ_w ((∑ x ∈ Finset.range (n + 2), (f x + 1))) ∈
        (M.StutterClosed).next (ρ_w ((∑ x ∈ Finset.range (n + 2), (f x + 1)) -1))
        (w ((∑ x ∈ Finset.range (n + 2), (f x + 1)) - 1)) := by
      have run := ρ_w_run.2 ((∑ x ∈ Finset.range (n + 2), (f x + 1)) - 1)
      rw [Nat.sub_add_cancel (by rw [Finset.sum_range_succ]; omega)] at run
      exact run

    unfold NA.next at ρ_w_next_spec
    unfold NPA.toNA at ρ_w_next_spec
    unfold NPA.StutterClosed at ρ_w_next_spec
    simp only at ρ_w_next_spec
    have eq : (∑ m : Fin (n+1), ((subset_wb_f_pair w ρ_w_pareven ↑m).2 + 1) + (Nat.find (subset_wb_f_pair._proof_1 w ρ_w_pareven (n+1)) - 1)) =
      (∑ x ∈ Finset.range (n + 2), (f x + 1) - 1) := by

      nth_rewrite 1 [Fin.sum_univ_eq_sum_range (fun m ↦ ((subset_wb_f_pair w ρ_w_pareven m).2 + 1)) (n+1)]
      nth_rewrite 2 [Finset.sum_range_succ]
      rw [hf]
      unfold subset_f
      simp only
      conv =>
        rhs
        unfold subset_wb_f_pair
        simp only

      conv =>
        lhs
        lhs
        unfold subset_wb_f_pair
        simp only
      rw [Nat.add_sub_assoc (by omega)]

      rw [Nat.add_right_inj]
      rw [Nat.add_sub_cancel]
    rw [← eq] at ρ_w_next_spec
    rw [hq] at ρ_w_next_spec
    simp at ρ_w_next_spec
    simp at k2_spec
    specialize  k2_spec q

    use q
    obtain ⟨_, state⟩ := ρ_w_next_spec
    rw [hk2] at k2_spec
    rw [← Nat.add_sub_assoc (k:=1) (by rw [← hk2]; omega)] at eq
    rw [← Nat.add_left_inj (n:=1)] at eq
    rw [Nat.sub_add_cancel (by rw [← hk2]; omega)] at eq
    rw [Nat.sub_add_cancel (by rw [Finset.sum_range_succ]; omega)] at eq
    rw [eq] at k2_spec
    nth_rewrite 2 [hf] at state
    apply Or.resolve_left state
    exact k2_spec


-- Claim 4.2.5
set_option pp.proofs true in
set_option pp.showLetValues true in
open Classical in
lemma subset_rhow'_pareven {M : NPA A} {w : Stream' A} {ρ_w : Stream' (M.StutterClosed).State}
    (ρ_w_run : M.StutterClosed.InfRun w ρ_w) {f f' : Stream' ℕ}
    (ρ_w_pareven : Even (sSup ((M.StutterClosed).parityMap '' InfOcc ρ_w)))
    (hf : f = subset_f w ρ_w_pareven) (hf' : f' = subset_f' ρ_w_run ρ_w_pareven hf) :
    let wb := subset_wb w ρ_w_pareven;
    Even (sSup ( M.parityMap '' (InfOcc (subset_rhow' ρ_w_run ρ_w_pareven hf)))) := by
  intro wb

  have hM : ∃ n, (∀ a ∈ (M.parityMap '' InfOcc (subset_rhow' ρ_w_run ρ_w_pareven hf)), a ≤ n) :=
      par_map_inf_occ_of_ss_has_sup M (subset_rhow' ρ_w_run ρ_w_pareven hf)

  have hMs : ∃ n, (∀ a ∈ ((M.StutterClosed).parityMap '' InfOcc ρ_w), a ≤ n) :=
    par_map_inf_occ_of_ss_has_sup M.StutterClosed ρ_w

  have ssuple: (sSup ( M.parityMap '' (InfOcc (subset_rhow' ρ_w_run ρ_w_pareven hf)))) + 2 ≤
       (sSup ((M.StutterClosed).parityMap '' InfOcc ρ_w)) := by
    rw [Nat.sSup_def hM]
    let sl := Nat.find hM
    have sl_spec : (∀ a ∈ (M.parityMap '' InfOcc (subset_rhow' ρ_w_run ρ_w_pareven hf)), a ≤ sl) :=
      Nat.find_spec hM

    have slinrange : sl ∈ M.parityMap '' (InfOcc (subset_rhow' ρ_w_run ρ_w_pareven hf)) := by
      unfold sl
      rw [← Nat.sSup_def hM]
      exact Nat.sSup_mem (Set.image_nonempty.mpr infoccnonemp) (bddAbove_def.mp hM)

    simp at slinrange
    obtain ⟨x, ⟨hxinf, hxsup⟩⟩ := slinrange
    have hxevent := @inf_occ_eventually (M.State) (M.FinState) (subset_rhow' ρ_w_run ρ_w_pareven hf)
    rw [Filter.eventually_atTop] at hxevent
    obtain ⟨idw', hidw'⟩ := hxevent

    unfold InfOcc at hxinf
    rw [Set.mem_setOf] at hxinf
    rw [Filter.frequently_atTop] at hxinf
    -- Nu kan je voor al die btjes een btje in rho_w geven of juist andersom. Eventjes andersom proberen

    -- rw [frequently_in_finite_set] at hxinf
    have hslininfoc : (sl + 2) ∈ (InfOcc ((M.StutterClosed.parityMap) ∘ ρ_w)) := by

      unfold InfOcc
      rw [Set.mem_setOf]
      rw [Filter.frequently_atTop]

      intro iwmin
      let ib := (Nat.find (kexists iwmin f))
      let iw'sum := ∑ m ∈ Finset.range (ib + 1), (f' m + 1)
      let idw'_b := (Nat.find (kexists idw' f'))
      let idw'_bsum := ∑ m ∈ Finset.range (idw'_b + 1), (f' m + 1)
      let iw'min := max iw'sum idw'_bsum
      -- Hier nog net iets verder specialiseren

      specialize hxinf (iw'min + 1)

      obtain ⟨iw', ⟨iw'ge, hiw'⟩⟩ := hxinf
      let iw'_b := (Nat.find (kexists (iw'-1) f'))
      have hiw'_b : iw'_b = (Nat.find (kexists (iw'-1) f')) := by
        unfold iw'_b
        exact rfl
      have hiw'2 := hiw'


      unfold subset_rhow' at hiw'
      simp only at hiw'

      unfold subset_f'_rhow'_pair at hiw'
      simp only at hiw'
      rw [hf'] at hiw'_b
      rw [← hiw'_b] at hiw'
      rw [← hf'] at hiw'_b

      split at hiw'

      case isTrue hfiwzero =>
        -- have spec1 := (subset_f'_rhow'_pair._proof_1 ρ_w_run ρ_w_pareven iw').choose_spec
        -- have spec2 := spec1.choose_spec

        sorry
      case isFalse hfiwnonzero =>

        simp at hiw'
        have fzero : f' iw'_b = 0 := by
          rw [hf']
          unfold subset_f'
          unfold subset_f'_rhow'_pair
          simp only [hfiwnonzero, ↓reduceDIte]


        have hone : iw' -  ∑ m ∈ Finset.range (iw'_b),
            (f' m + 1) = 1 := by

          have hiw'_b2 := hiw'_b
          rw [Nat.find_eq_iff] at hiw'_b

          unfold n_lt_sumk at hiw'_b
          obtain ⟨hiw'_b, right⟩ := hiw'_b

          rw [Finset.sum_range_succ] at hiw'_b
          rw [← hiw'_b2] at hiw'_b
          rw [fzero] at hiw'_b
          simp at hiw'_b
          rw [add_comm] at hiw'_b
          rw [← Nat.sub_lt_iff_lt_add (by sorry)] at hiw'_b
          rw [Nat.lt_one_iff] at hiw'_b
          rw [Nat.sub_right_comm] at hiw'_b
          rw [← Nat.add_right_cancel_iff (n:=1)] at hiw'_b
          rw [← hiw'_b2] at right
          specialize right (iw'_b-1)
          simp at right
          rw [Nat.sub_add_cancel (by sorry)] at hiw'_b
          exact hiw'_b

        rw [← hf'] at hiw'
        rw [hone] at hiw'
        simp only [↓reduceIte] at hiw'


        use (∑ m ∈ Finset.range (iw'_b + 1), (f m + 1))

        -- Nu laten zien dat dat die toestand is, dat is moeilijk maar gaan we regelen
        -- Nu laten zien met de nat.find dat je in een (q, omega(q)) toestand zit

        have hfiwnonzero2 : f iw'_b ≥ 1 := by omega

        rw [hf] at hfiwnonzero2
        unfold subset_f at hfiwnonzero2
        simp only [ge_iff_le] at hfiwnonzero2
        unfold subset_wb_f_pair at hfiwnonzero2
        simp only at hfiwnonzero2
        rw [Nat.le_sub_one_iff_lt (by omega)] at hfiwnonzero2
        rw [← Nat.add_one_le_iff] at hfiwnonzero2

        simp only [Nat.reduceAdd] at hfiwnonzero2

        simp at hfiwnonzero2
        specialize hfiwnonzero2 1
        simp at hfiwnonzero2
        obtain ⟨q, hq⟩ := sumpointseqnumstate f ρ_w_run ρ_w_pareven hf iw'_b
          (by apply Nat.pos_iff_ne_zero.mpr hfiwnonzero)

        have stateone : (ρ_w (∑ m ∈ Finset.range (iw'_b + 1), (f m + 1))).1 = q := by
          simp only [hq]

        rw [hiw'_b] at stateone
        rw [← stateone] at hq
        constructor
        · have basebig : iw'_b + 1 ≥ ib + 1:= by
            refine Nat.add_le_add (c:= 1) (d:= 1) ?_ (by trivial)
            unfold iw'_b
            have iw'big : iw' - 1 ≥ iw'sum := by omega
            unfold iw'sum at iw'big
            rw [Nat.le_find_iff]
            intro m
            intro hm
            unfold n_lt_sumk
            simp only [not_lt]

            have sumgt : (∑ m ∈ Finset.range (m + 1), (f' m + 1)) ≤  (∑ m ∈ Finset.range (ib + 1), (f' m + 1))  := by
              -- aesop
              sorry

            apply GE.ge.le at iw'big
            apply ge_trans iw'big
            exact sumgt
          rw [← Nat.sub_add_cancel basebig]
          rw [add_comm]
          rw [Finset.sum_range_add]
          have hib : ib = Nat.find (kexists (iwmin) f) := by unfold ib; exact rfl
          have hib2 := hib
          rw [Nat.find_eq_iff] at hib
          unfold n_lt_sumk at hib
          rw [← hib2] at hib
          -- have ge : ∑ x ∈ Finset.range (iw'_b + 1 - (ib + 1)), (f (ib + 1 + x) + 1) ≥ 1 := by sorry
          apply LE.le.ge
          apply Nat.le_add_right_of_le
          apply Nat.le_of_lt
          exact hib.1
        · simp only [Function.comp_apply]
          unfold NPA.parityMap
          unfold NPA.StutterClosed
          simp [hq]
          rw [hiw']
          exact hxsup

    rw [infOcc_comp_of_Finite ((M.StutterClosed).FinState) ] at hslininfoc

    rw [Set.mem_image] at hslininfoc
    obtain ⟨q, ⟨hqinf, hqomega⟩⟩ := hslininfoc

    rw [Nat.sSup_def hMs]
    rw [Nat.le_find_iff]
    intro m
    intro hm
    simp only [Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, not_forall,
          not_le]

    use q
    unfold sl at hqomega
    rw [hqomega]
    exact ⟨hqinf, hm⟩

  have ssupge: (sSup ( M.parityMap '' (InfOcc (subset_rhow' ρ_w_run ρ_w_pareven hf)))) + 2 ≥
       (sSup ((M.StutterClosed).parityMap '' InfOcc ρ_w)) := by sorry

  have ssupsame: (sSup ( M.parityMap '' (InfOcc (subset_rhow' ρ_w_run ρ_w_pareven hf)))) + 2 =
       (sSup ((M.StutterClosed).parityMap '' InfOcc ρ_w)) := le_antisymm_iff.2 ⟨ssuple, ssupge⟩

  apply Classical.by_contradiction
  intro hypo
  simp at hypo

  have ssupodd: Odd ((sSup ( M.parityMap '' (InfOcc (subset_rhow' ρ_w_run ρ_w_pareven hf)))) + 2) :=
    Odd.add_even hypo even_two

  rw [ssupsame] at ssupodd

  rw [← Nat.not_even_iff_odd] at ssupodd
  exact ssupodd ρ_w_pareven



-- Proof Supset
-- Definition 4.2.6
noncomputable def supset_rhowb {M : NPA A} (ρ_w' : Stream' M.State) (f : Stream' ℕ) :
    Stream' (M.StutterClosed).State
| k =>
    if k = 0 then
      (ρ_w' 0 , Sum.inr ⟨(M.parityMap (ρ_w' 0)), inrange (ρ_w' 0)⟩)
    else if f (k - 1) = 0 then
      let q : M.State := ρ_w' ((∑ m ∈ Finset.range k, (f m + 1)))
      (q, Sum.inr ⟨(M.parityMap q), inrange q⟩)
    else
      let start : ℕ := ∑ m ∈ Finset.range (k-1), (f m + 1)
      let maxp : ℕ := sSup (M.parityMap '' (ρ_w' '' {l | (start < l) ∧ (l ≤ (start + f (k - 1) + 1))}))
      ( ρ_w' (start + f (k - 1) + 1)
      , Sum.inr ⟨maxp, by unfold maxp; exact ssupinrange (inpnonemp ρ_w' start (f (k - 1) + 1) (by simp)) (inpfinite ρ_w' start (f (k- 1) + 1))⟩)

noncomputable def parmap_sup_decidable (M : NPA A) (ss : Stream' M.State) (n: ℕ) : Decidable  (∀ a ∈ (M.parityMap '' InfOcc ss), a ≤ n) := by
  have := @Fintype.decidableForallFintype (M.parityMap '' InfOcc ss) (· ≤ n) _
  have inpfin : Fintype ↑(NPA.parityMap '' InfOcc ss) := by
    have infoccfinite : Fintype (InfOcc ss) := by
      unfold InfOcc
      exact @Fintype.ofFinite {x | ∃ᶠ (k : ℕ) in Filter.atTop, ss k = x} <|
        Set.Finite.subset (@Set.finite_univ M.State M.FinState) (fun ⦃a⦄ a ↦ trivial)
    refine (InfOcc ss).fintypeImage NPA.parityMap
  simp only [Subtype.forall] at this
  apply this

-- Definition 4.2.9
-- Here the pattern matching apperently does not work to show termination
-- Setting: w = wb[f], w' = wb[f']. Dan ss is run op wb en ss' is run op w'
noncomputable def supset_rhow {A : Type} {M : NPA A} (ρ_wb : Stream' (M.StutterClosed).State)
    (ρ_w' : Stream' M.State) (w : Stream' A) (f f' : Stream' ℕ) (k : ℕ) : (M.StutterClosed).State :=
  if k = 0 then
    ρ_wb 0
  else
    let k_b : ℕ :=  Nat.find (kexists (k-1) f)
    if fkb_zero : f k_b = 0 then
      ρ_wb (k_b + 1)
    else
      let i := k - ∑ m∈ Finset.range (k_b), (f m + 1) + 1 -- denk niet +1
      have dec: Decidable (((ρ_wb (k_b + 1)).1, Sum.inl (w k)) ∈ ((M.StutterClosed).next (supset_rhow ρ_wb ρ_w' w f f' (k - 1)) (w k))) := by sorry
      if h: ((ρ_wb (k_b + 1)).1, Sum.inl (w k)) ∈ ((M.StutterClosed).next (supset_rhow ρ_wb ρ_w' w f f' (k - 1)) (w k)) then
        if k+1 = ∑ m∈ Finset.range (k_b + 1), (f m + 1) then
          ((ρ_wb (k_b + 1)).1, Sum.inr ⟨M.parityMap (ρ_wb (k_b + 1)).1, by simp only [Set.mem_range,
            exists_apply_eq_apply]⟩)
        else
          ((ρ_wb (k_b + 1)).1, Sum.inl (w k))
      else
        if hdiff1: f k_b ≤ f' k_b then
          if k+1 = ∑ m∈ Finset.range (k_b + 1), (f m + 1) then
            if hdiff2: f k_b = f' k_b then
              (ρ_w' (∑ m∈ Finset.range (k_b + 1), (f' m + 1) - 1), Sum.inr ⟨M.parityMap (ρ_w' (∑ m∈ Finset.range (k_b + 1), (f' m + 1) - 1)), by simp⟩)
            else
              let start := i + ∑ m∈ Finset.range (k_b), (f' m + 1)
              let diff := f' k_b - f k_b
              let maxp : ℕ := sSup (M.parityMap '' (ρ_w' '' {l | (start < l) ∧ (l ≤ (start + diff))}))
              ((ρ_w' (start + diff))
              , Sum.inr ⟨maxp, by unfold maxp; exact ssupinrange (inpnonemp ρ_w' start diff (by omega)) (inpfinite  ρ_w' start diff)⟩)
          else
            (ρ_w' (i + ∑ m∈ Finset.range (k_b), (f' m + 1)), Sum.inr ⟨M.parityMap (ρ_w' (i + ∑ m∈ Finset.range (k_b), (f' m + 1))), by simp⟩)
        else
          if hi: i <= f' k_b then
            (ρ_w' (i + ∑ m∈ Finset.range (k_b), (f' m + 1)), Sum.inr ⟨M.parityMap (ρ_w' (i + ∑ m∈ Finset.range (k_b), (f' m + 1))), by simp⟩)
          else
            -- by exfalso
            -- sorry
            -- bewijs hier dat dat niet gebeurt
            if k+1 = ∑ m∈ Finset.range (k_b + 1), (f m + 1) then
              ((ρ_wb (k_b + 1)).1, Sum.inr ⟨M.parityMap (ρ_wb (k_b + 1)).1, by simp only [Set.mem_range,
                exists_apply_eq_apply]⟩)
            else
              ((ρ_wb (k_b + 1)).1, Sum.inl (w k))

-- Lemmas for claim 4.2.7
lemma rhowb_sumcorrect {A : Type} {M : NPA A} (f' : Stream' ℕ) (ρ_w' : Stream' (M.State)) :
    ∀ (k : ℕ), (supset_rhowb ρ_w' f' k).1 = ρ_w' (∑ m ∈ Finset.range k, (f' m + 1)) := by
  intro k
  cases' k with n
  · unfold supset_rhowb
    simp only [↓reduceIte, Finset.range_zero, Finset.sum_empty]
  · simp only [supset_rhowb, Nat.add_eq_zero, one_ne_zero, and_false, ↓reduceIte,
               add_tsub_cancel_right]
    if h1 : (f' n) = 0 then
      simp only [↓reduceIte, h1]
    else
      simp only [↓reduceIte, h1]
      apply congrArg
      rw [Finset.sum_range_succ, add_assoc]

lemma rhowb_numstate {A : Type} {M : NPA A} (f' : Stream' ℕ) (ρ_w' : Stream' (M.State)) (k : ℕ) :
    let ρ_wb := supset_rhowb ρ_w' f'; (ρ_wb k).1 = ρ_w' (∑ m ∈ Finset.range k, (f' m + 1)) →
    ∃ p, (ρ_wb k).2 = Sum.inr p := by
  intro ρ_wb hk
  cases' k with n
  · unfold ρ_wb supset_rhowb
    simp only [↓reduceIte, Sum.inr.injEq, exists_eq']
  · unfold ρ_wb supset_rhowb
    simp only [Nat.add_eq_zero, one_ne_zero, and_false, ↓reduceIte, add_tsub_cancel_right,
      Subtype.exists, Set.mem_range]
    if h1 : (f' n) = 0 then
      simp only [↓reduceIte, h1, Sum.inr.injEq, Subtype.mk.injEq, exists_prop, exists_eq_right',
        exists_apply_eq_apply]
    else
      simp only [↓reduceIte, h1, Sum.inr.injEq, Subtype.mk.injEq, exists_prop, exists_eq_right']
      refine @ssupinrange A M ((ρ_w' '' {l | ∑ m ∈ Finset.range n, (f' m + 1) < l ∧ l ≤ ∑ m ∈ Finset.range n, (f' m + 1) + f' n + 1})) ?_ ?_
      · simp only [Set.image_nonempty]
        refine Set.nonempty_of_mem (x:= (∑ m ∈ Finset.range n, (f' m + 1) + f' n + 1)) ?_
        · simp only [Set.mem_setOf, add_assoc, lt_add_iff_pos_right, add_pos_iff, zero_lt_one, or_true, le_refl,
            and_self]
      · apply Set.Finite.image ρ_w'
        refine' Set.Finite.subset (s:= {l | l ≤ ∑ m ∈ Finset.range n, (f' m + 1) + f' n + 1}) ?_ ?_
        · exact (Set.finite_le_nat (∑ m ∈ Finset.range n, (f' m + 1) + f' n + 1))
        · exact (Set.sep_subset_setOf (∑ m ∈ Finset.range n, (f' m + 1)).succ.le fun x ↦
              x ≤ ∑ m ∈ Finset.range n, (f' m + 1) + f' n + 1)

lemma inpsame {A : Type} {M : NPA A} (f' : Stream' ℕ) (ρ_w' : Stream' (M.State)) (k : ℕ) :
    ρ_w' '' {l | ∑ m ∈ Finset.range k, (f' m + 1) < l ∧ l ≤ ∑ m ∈ Finset.range k, (f' m + 1) + f' k + 1} =
    Stream'.drop (∑ m ∈ Finset.range k, (f' m + 1)) ρ_w' '' {k_1 | k_1 > 0 ∧ k_1 ≤ f' k + 1} := by
  unfold Stream'.drop
  unfold Stream'.get
  unfold Set.image
  apply Set.ext_iff.2
  intro x
  repeat rw [Set.mem_setOf]
  refine ⟨?_,?_⟩
  · intro h
    obtain ⟨a, ⟨ha, ssax⟩⟩:=h
    rw [Set.mem_setOf] at ha
    use a - ∑ m ∈ Finset.range k, (f' m + 1)
    constructor
    · rw [add_assoc, add_comm] at ha
      apply Set.mem_setOf.2
      simpa only [gt_iff_lt, tsub_pos_iff_lt, tsub_le_iff_right] using ha
    · simpa only [add_comm, Nat.add_sub_cancel' (le_of_lt ha.1)] using ssax

  · intro h
    obtain ⟨a, ⟨ha, ssax⟩⟩:=h
    use (a + ∑ m ∈ Finset.range k, (f' m + 1))
    constructor
    · rw [Set.mem_setOf]
      apply Set.mem_setOf.1 at ha
      simp only [lt_add_iff_pos_left, add_assoc]
      rw [add_comm]
      simpa only [add_le_add_iff_left] using ha
    · simp only [ssax]

-- Claim 4.2.7
lemma supset_rhowb_run {A : Type} {M : NPA A} {w' wb : Stream' A} {ρ_w' : Stream' M.State}
    {f' : Stream' ℕ} (ρ_w'_run : M.InfRun w' ρ_w') (w'_wbf : w' = functiononword wb f') :
    let ρ_wb := supset_rhowb ρ_w' f'; (M.StutterClosed).InfRun wb ρ_wb := by
  intro ρ_wb
  rw [NA.InfRun]
  obtain ⟨ρ_w'_init, ρ_w'_next⟩ := ρ_w'_run

  constructor
  · exact Set.mem_setOf.2 ⟨ρ_w' 0, ρ_w'_init, rfl⟩
  · intro k

    conv =>
      rhs
      simp only [ρ_wb, supset_rhowb]
    simp only [Nat.add_eq_zero, one_ne_zero, and_false, ↓reduceIte, Nat.add_one_sub_one]
    if h1 : (f' k) = 0  then
      simp only [h1, ↓reduceIte]
      rw [← Prod.eta (ρ_wb k), (rhowb_sumcorrect f' ρ_w' )]
      rcases rhowb_numstate f' ρ_w' k (rhowb_sumcorrect f' ρ_w' k) with ⟨p, hp⟩
      rw [hp, Finset.sum_range_succ, h1, zero_add]
      unfold NA.next NPA.toNA NPA.StutterClosed
      simp only [Set.mem_union]
      refine Or.inl (Or.inl ?_)
      simp only [Set.mem_setOf_eq, Prod.mk.injEq, Sum.inr.injEq, Subtype.mk.injEq, existsAndEq,
        and_self, and_true]
      rw [← functiononword_eq_base_word (b:=0) w'_wbf k (by linarith), zero_add]
      exact ρ_w'_next (∑ m ∈ Finset.range k, (f' m + 1))

    else
      simp only [h1, ↓reduceIte]
      rw [← Prod.eta (ρ_wb k), (rhowb_sumcorrect f' ρ_w' )]
      rcases rhowb_numstate f' ρ_w' k (rhowb_sumcorrect f' ρ_w' k) with ⟨p, hp⟩
      rw [hp]
      unfold NA.next NPA.toNA NPA.StutterClosed
      simp only [Set.mem_union]
      right
      nth_rewrite 1 [add_assoc]
      apply Set.mem_setOf.2
      use (f' k + 1)
      use Stream'.drop (∑ m ∈ Finset.range k, (f' m + 1)) ρ_w'
      refine ⟨?_, ⟨?_, ?_⟩⟩
      · simp only [ge_iff_le, le_add_iff_nonneg_left, zero_le]
      · unfold NA.FinRunStart
        refine ⟨?_, ?_⟩
        · unfold Stream'.drop Stream'.get
          simp only [zero_add]
        · intro b hb
          unfold Stream'.drop Stream'.get
          simp only
          rw [← functiononword_eq_base_word w'_wbf k hb, add_right_comm]
          exact ρ_w'_next  (b + ∑ m ∈ Finset.range k, (f' m + 1))
      · simp only [gt_iff_lt, Sum.inr.injEq, Subtype.mk.injEq]
        exact ⟨congrArg sSup (congrArg (Set.image M.parityMap) (inpsame f' ρ_w' k)),
               Eq.symm Stream'.get_drop'⟩

-- Lemmas for claim 4.2.8


-- Claim 4.2.8
open Classical in
lemma supset_rhowb_pareven {A : Type} {M : NPA A} (w : Stream' A) (f : Stream' ℕ) {f' : Stream' ℕ}
    {w' wb : Stream' A} {ρ_w' : Stream' M.State}
    (ρ_w'_run : M.InfRun w' ρ_w') (ρ_w'_pareven : Even (sSup (M.parityMap '' InfOcc ρ_w')))
    (w'_wbf : w' = functiononword wb f') :
    let ρ_wb := supset_rhowb ρ_w' f';
    Even (sSup ((M.StutterClosed).parityMap '' InfOcc ρ_wb)) := by
  intro ρ_wb
  let Ms := (M.StutterClosed)

  have samesup : sSup (M.parityMap '' InfOcc ρ_w') + 2 = sSup ((M.StutterClosed).parityMap '' InfOcc (supset_rhowb ρ_w' f')) := by
    have hMs : ∃ n, (∀ a ∈ (Ms.parityMap '' InfOcc ρ_wb), a ≤ n) :=
      par_map_inf_occ_of_ss_has_sup Ms ρ_wb

    rw [Nat.sSup_def hMs]
    have hM : ∃ n, (∀ a ∈ (M.parityMap '' InfOcc ρ_w'), a ≤ n) :=
      par_map_inf_occ_of_ss_has_sup M ρ_w'

    rw [Nat.sSup_def hM]

    -- Iets met +2 aanpassen
    --- goed hierover nadenken nog...
    rw [le_antisymm_iff]
    constructor
    · simp

      intro m hm
      rw [← tsub_lt_iff_right] at hm
      rw [Nat.lt_find_iff] at hm
      simp at hm
      unfold NPA.parityMap
      unfold Ms
      unfold NPA.StutterClosed

      simp only [decide_eq_true_eq, Prod.exists, Sum.exists, Sum.elim_inl, Nat.lt_one_iff,
        exists_and_right, Sum.elim_inr, Subtype.exists, Set.mem_range]
      specialize hm (m-2)
      simp at hm
      obtain ⟨x, hx⟩ := hm
      use x
      right
      use M.parityMap x
      constructor
      · sorry
      · rw [← tsub_lt_iff_right]
        exact hx.2
        sorry


      sorry
    · sorry

  rw [← samesup]
  apply Even.add ρ_w'_pareven even_two


-- Lemmas for waccepted
-- Claim 4.2.10
lemma supset_rhow_run {A : Type} {w wb w' : Stream' A} {M : NPA A} {f : Stream' ℕ}
    {ρ_wb : Stream' (M.StutterClosed).State} {ρ_w' : Stream' M.State} (hw : w = functiononword wb f)
    (f' : Stream' ℕ) (ρ_wb_pareven : Even (sSup ((M.StutterClosed).parityMap '' InfOcc ρ_wb)))
    (ρ_wb_run : M.StutterClosed.InfRun wb ρ_wb)
    (ρ_w'_pareven : Even (sSup (M.parityMap '' InfOcc ρ_w')))
    (ρ_w'run : M.InfRun w' ρ_w') : M.StutterClosed.InfRun w (supset_rhow ρ_wb ρ_w' w f f') := by
  unfold NA.InfRun
  obtain ⟨ρ_wb_init, ρ_wb_next⟩ := ρ_wb_run
  constructor
  · unfold supset_rhow
    simp only [↓reduceIte]
    exact ρ_wb_init
  · intro k

    unfold supset_rhow

    cases k
    ·
      -- zero_add, one_ne_zero, tsub_self, Nat.reduceAdd, Nat.add_one_sub_one,
      -- dite_eq_ite]



      -- , zero_add, one_ne_zero, tsub_self, Nat.reduceAdd, Nat.add_one_sub_one,
      -- dite_eq_ite]

      sorry
    · sorry

-- Claim 4.2.11
lemma supset_rhow_pareven {A : Type} {w wb w' : Stream' A} {M : NPA A} {f : Stream' ℕ}
    {ρ_wb : Stream' (M.StutterClosed).State} {ρ_w' : Stream' M.State} (hw : w = functiononword wb f)
    (f' : Stream' ℕ) (ρ_wb_pareven : Even (sSup ((M.StutterClosed).parityMap '' InfOcc ρ_wb)))
    (ρ_wb_run : M.StutterClosed.InfRun wb ρ_wb)
    (ρ_w'_pareven : Even (sSup (M.parityMap '' InfOcc ρ_w'))) (ρ_w'_run : M.InfRun w' ρ_w') :
    Even (sSup ((M.StutterClosed).parityMap '' InfOcc (supset_rhow ρ_wb ρ_w' w f f'))) := by sorry

-- Full theorem
theorem NA.StutterClosurerecognizesStutterClosure (M : NPA A) :
    (M.StutterClosed).AcceptedOmegaLang = StutterClosure (M.AcceptedOmegaLang) := by
  ext w
  constructor
  · intro hwinlang
    rw [NPA.AcceptedOmegaLang] at hwinlang ⊢
    rw [Set.mem_setOf, NPA.ParityAccept] at hwinlang
    rw [StutterClosure, Set.mem_setOf]
    obtain ⟨ρ_w, ⟨ρ_w_run, ρ_w_pareven⟩⟩ := hwinlang
    let wb := subset_wb w ρ_w_pareven
    let f := subset_f w ρ_w_pareven
    let f' := subset_f' ρ_w_run ρ_w_pareven (f:=f) (by trivial)
    let ρ_w' := subset_rhow' ρ_w_run ρ_w_pareven (f:=f) (by trivial)
    use (functiononword wb f')
    rw [Set.mem_setOf]
    unfold NPA.ParityAccept
    constructor
    · use ρ_w'
      exact ⟨subset_rhow'_run ρ_w_run ρ_w_pareven (by trivial) (by trivial) (by trivial), subset_rhow'_pareven ρ_w_run ρ_w_pareven
                                                    (by trivial) (by trivial)⟩
    · exact subset_stutequiv_w_w' ρ_w_run ρ_w_pareven (by trivial)
  · intro hwinlang
    rw [StutterClosure] at hwinlang
    apply Membership.mem.out at hwinlang
    obtain ⟨w', ⟨hw'inlang, ⟨wb, f, f', hwb⟩⟩⟩ := hwinlang
    rw [NPA.AcceptedOmegaLang, Set.mem_setOf, NPA.ParityAccept] at hw'inlang ⊢
    obtain ⟨ρ_w', ⟨ρ_w'_run , ρ_w'_pareven⟩⟩ := hw'inlang
    let ρ_wb := supset_rhowb ρ_w' f';
    obtain ρ_wb_run := supset_rhowb_run ρ_w'_run hwb.2
    obtain ρ_wb_pareven := supset_rhowb_pareven w f  ρ_w'_run ρ_w'_pareven hwb.2
    use supset_rhow ρ_wb ρ_w' w f f'
    exact ⟨supset_rhow_run hwb.1 f' ρ_wb_pareven ρ_wb_run ρ_w'_pareven ρ_w'_run,
          supset_rhow_pareven hwb.1 f' ρ_wb_pareven ρ_wb_run ρ_w'_pareven ρ_w'_run⟩

    -- Meer BFS approach, eerst bewijs uittypen, sorrys niet zo erg maar in het midden Voor volgende week deze sorry weg
    -- In abstract eerlijk zijn
    -- 17 november eerste deadline voor hoofdstuk 5

end Automata

#eval let f : Stream' ℕ := (fun i ↦ if i = 1 then 0 else if i = 0 then 0 else if i = 2 then 2 else 0); ∑ m∈ Finset.range 5, (f m + 1)
