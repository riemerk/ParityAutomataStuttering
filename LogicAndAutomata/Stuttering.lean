import Mathlib

variable {Alph : Type}

abbrev n_lt_sumk (n : ℕ) (f : Stream' ℕ) (k : Nat) : Prop :=
       (n < (∑ m∈ Finset.range (k + 1), (f m + 1)))

lemma fstrictmono (f : Stream' ℕ) : StrictMono fun k ↦ (∑ m∈Finset.range k, (f m + 1)) := by
  refine strictMono_nat_of_lt_succ ?_
  intro m
  simp only [Finset.sum_range_succ, lt_add_iff_pos_right, add_pos_iff, zero_lt_one, or_true]

theorem kexists (n : ℕ) (f : Stream' ℕ) : ∃k, (n_lt_sumk n f k) := by
  have exists_k_above_n: ∃ k, n + 1 ≤ ∑ m ∈ Finset.range (k), (f m + 1) := by
    apply (Filter.tendsto_atTop_atTop_iff_of_monotone (fstrictmono f).monotone).1
    exact StrictMono.tendsto_atTop (fstrictmono f)
  have h' m := Nat.find_min exists_k_above_n (m := m)
  simp only [not_le] at h'
  use Nat.find exists_k_above_n - 1

  simp only [gt_iff_lt, Nat.le_find_iff, Nat.lt_one_iff, not_le, forall_eq, Finset.range_zero,
    Finset.sum_empty, add_pos_iff, zero_lt_one, or_true, Nat.sub_add_cancel]
  apply Nat.lt_of_add_one_le
  simp only [Nat.find_spec exists_k_above_n]


def functiononword (w : Stream' Alph) (f : Stream' ℕ) (n : ℕ) : Alph:=
  let l : ℕ := Nat.find (kexists n f)
  w l

def StutterEquivalent (w : Stream' Alph) (w' : Stream' Alph) : Prop :=
  ∃ wb : Stream' Alph,  ∃ f : Stream' ℕ,  ∃ f' : Stream' ℕ,
    w = (functiononword wb f) ∧ w' = (functiononword wb f')

def StutterClosure (L : Set (Stream' Alph)) : Set (Stream' Alph) :=
  {w | ∃ w' ∈ L, (StutterEquivalent w w')}

lemma functiononword_eq_base_word {w wb : Stream' Alph} {b : ℕ} {f : Stream' ℕ}
      (hw : w = functiononword wb f) (k : ℕ) (hb : b < f k + 1) :
      w (b + ∑ m ∈ Finset.range k, (f m + 1)) = wb k := by
  rw [hw]
  unfold functiononword
  simp only
  apply congrArg
  induction k generalizing b
  case zero =>
    simp only [Finset.range_zero, Finset.sum_empty, add_zero, Nat.find_eq_zero, gt_iff_lt,
    zero_add, Finset.range_one, Finset.sum_singleton, hb]
  case succ d hd =>
    rw [(Nat.find_eq_iff (kexists (b + ∑ m ∈ Finset.range (d+1), (f m + 1)) f))]
    constructor
    · simp only [gt_iff_lt]
      nth_rewrite 2 [Finset.sum_range_succ]
      rw [add_comm]
      exact Nat.add_lt_add_left hb (∑ m ∈ Finset.range (d + 1), (f m + 1))
    · intro n hn
      if hn2: n < d then
        intro h
        have bigger: b + ∑ m ∈ Finset.range (d + 1), (f m + 1) > ∑ m ∈ Finset.range (d), (f m + 1)
              := by rw [Finset.sum_range_succ]; linarith
        have notnbigger : ¬ (∑ m ∈ Finset.range (d), (f m + 1) <
                          ∑ m ∈ Finset.range (n+1), (f m + 1)) := by
          have p0: 0 + ∑ m ∈ Finset.range d, (f m + 1) < ∑ m ∈ Finset.range (d + 1), (f m + 1) ∧
               ∀ n < d, ¬0 + ∑ m ∈ Finset.range d, (f m + 1) < ∑ m ∈ Finset.range (n + 1), (f m + 1)
              := by
            specialize @hd 0
            rw [← (Nat.find_eq_iff (kexists (0 + ∑ m ∈ Finset.range (d), (f m + 1)) f))]
            exact hd (by simp)

          obtain ⟨a, b⟩:=p0
          simp only [zero_add] at b
          apply b
          exact hn2

        exact notnbigger (Nat.lt_trans bigger h)

      else
        have neq : n = d:= by
          simp only [not_lt] at hn2
          exact Nat.eq_of_le_of_lt_succ hn2 hn
        simp only [not_lt, ge_iff_le]
        rw [neq]
        exact Nat.le_add_left (∑ m ∈ Finset.range (d + 1), (f m + 1)) b
