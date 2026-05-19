import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Finset

theorem Icc_eq_Ico (a b : ℕ) : Icc a b = Ico a (b + 1) := by
  ext n
  simp

theorem sum_Icc_eq_sum_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (a b : ℕ) :
    (∑ k ∈ Icc a b, f k) = ∑ k ∈ range (b + 1 - a), f (a + k) := by
  rw [Icc_eq_Ico]
  exact sum_Ico_eq_sum_range f a (b + 1)

end Finset

namespace Nat

theorem sq_sqrt_le (n : ℕ) : n.sqrt ^ 2 ≤ n := Nat.sqrt_le' n

end Nat


/-- Parser-stable shorthand for the integer non-divisibility side condition. -/
def IntNotDvd (p : ℕ) (h : ℤ) : Prop := ¬ ∃ q : ℤ, h = (p : ℤ) * q

lemma abs_add (a b : ℝ) : |a + b| ≤ |a| + |b| := abs_add_le a b

lemma abs_sum_le_sum_abs {α : Type*} [DecidableEq α] {s : Finset α} (f : α → ℝ) :
    |∑ x ∈ s, f x| ≤ ∑ x ∈ s, |f x| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      simp [ha]
      exact le_trans (abs_add_le (f a) (∑ x ∈ s, f x)) (add_le_add_right ih _)

lemma le_div_iff {a b c : ℝ} (hc : 0 < c) : a ≤ b / c ↔ a * c ≤ b := le_div_iff₀ hc

lemma mul_sum {α : Type*} [DecidableEq α] {s : Finset α} (c : ℝ) (f : α → ℝ) :
    c * (∑ x ∈ s, f x) = ∑ x ∈ s, c * f x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [ha, ih, left_distrib]

lemma sum_mul {α : Type*} [DecidableEq α] {s : Finset α} (f : α → ℝ) (c : ℝ) :
    (∑ x ∈ s, f x) * c = ∑ x ∈ s, f x * c := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [ha, ih, right_distrib]

noncomputable section

namespace FixedShiftLiouville

section ShortBlock

/-- Prefix sums attached to a real sequence. -/
def A (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), a n

/--
Short block sum.

This is the Lean-normalized form of the paper's `∑_{x < n ≤ x+H} a(n)`.
-/
def B (a : ℕ → ℝ) (x H : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc (x + 1) (x + H), a n

/-- Short-block energy. -/
def E (a : ℕ → ℝ) (X M : ℕ) : ℝ :=
  ∑ x ∈ Finset.Icc X (2 * X - M), (B a x M)^2

/-- Pointwise boundedness hypothesis abstracting `|a(n)| ≤ 1`. -/
def BoundedByOne (a : ℕ → ℝ) : Prop :=
  ∀ n, |a n| ≤ 1

/-- The critical scale `H = ⌊X^{1/2}⌋`. -/
def criticalScale (X : ℕ) : ℕ :=
  Nat.sqrt X

/-- The quantitative short-block hypothesis from Section 2. -/
def CriticalShortBlockHyp (a : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ X₀ : ℕ, ∀ ⦃X : ℕ⦄, X₀ ≤ X →
    E a X (criticalScale X) ≤ ε * X * (criticalScale X)^2

/-- Local prefix control on each dyadic window `[X,2X]`. -/
def DyadicLocalControl (a : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ X₀ : ℕ, ∀ ⦃X N : ℕ⦄, X₀ ≤ X →
    N ∈ Finset.Icc X (2 * X) → |A a N - A a X| ≤ ε * X

/-- The final `o(N)` conclusion, written in epsilon form. -/
def PrefixLittleO (a : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N₀ : ℕ, ∀ ⦃N : ℕ⦄, N₀ ≤ N → |A a N| ≤ ε * N

/-- A generic sublinearity interface for scale functions `H(X)`. -/
def ScaleSublinear (H : ℕ → ℕ) : Prop :=
  ∀ ε > 0, ∃ X₀ : ℕ, ∀ ⦃X : ℕ⦄, X₀ ≤ X → (H X : ℝ) ≤ ε * X

/-- The telescope identity `B = A(x+H) - A(x)`. -/
lemma B_eq_A_sub (a : ℕ → ℝ) {x H : ℕ} :
    B a x H = A a (x + H) - A a x := by
  unfold B A
  rw [show Finset.Icc (x + 1) (x + H) = Finset.Ico (x + 1) (x + H + 1) by
    simp [Finset.Icc_eq_Ico]]
  rw [Finset.sum_Ico_eq_sub (f := a) (by omega)]

@[simp] lemma B_zero (a : ℕ → ℝ) (x : ℕ) : B a x 0 = 0 := by
  unfold B
  simp

/-- The bad set of starting points at threshold `τ`. -/
def badSet (a : ℕ → ℝ) (X H : ℕ) (τ : ℝ) : Finset ℕ :=
  (Finset.Icc X (2 * X - H)).filter (fun x => τ * H < |B a x H|)

/-- The `r`-th residue fiber of the bad set modulo `H`, after translating by `X`. -/
def badSetResidue (a : ℕ → ℝ) (X H : ℕ) (τ : ℝ) (r : ℕ) : Finset ℕ :=
  (badSet a X H τ).filter (fun x => (x - X) % H = r)

/-- The starting point of the `j`-th block in residue class `r mod H`. -/
def progressionStart (X H r j : ℕ) : ℕ :=
  X + r + j * H

/-- The bad blocks among the first `m` blocks of a chosen residue class. -/
def badBlocksOnProgression
    (a : ℕ → ℝ) (X H : ℕ) (τ : ℝ) (r m : ℕ) : Finset ℕ :=
  (Finset.range m).filter (fun j => τ * H < |B a (progressionStart X H r j) H|)

lemma abs_sum_le_card_mul_bound
    {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℝ) {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ x ∈ s, |f x| ≤ C) :
    |∑ x ∈ s, f x| ≤ (s.card : ℝ) * C := by
  calc
    |∑ x ∈ s, f x| ≤ ∑ x ∈ s, |f x| := by
      simpa using abs_sum_le_sum_abs (fun x => f x)
    _ ≤ ∑ _x ∈ s, C := by
      refine Finset.sum_le_sum ?_
      intro x hx
      exact hf x hx
    _ = (s.card : ℝ) * C := by
      simp

/-- Uniform `L^∞` control on a short block from pointwise boundedness. -/
lemma abs_B_le
    {a : ℕ → ℝ} (ha : BoundedByOne a) (x H : ℕ) :
    |B a x H| ≤ H := by
  calc
    |B a x H| ≤ ∑ n ∈ Finset.Icc (x + 1) (x + H), |a n| := by
      unfold B
      simpa using abs_sum_le_sum_abs (fun n => a n)
    _ ≤ ∑ _n ∈ Finset.Icc (x + 1) (x + H), (1 : ℝ) := by
      refine Finset.sum_le_sum ?_
      intro n hn
      exact ha n
    _ = H := by
      simp

/-- A trivial bound on a prefix sum from pointwise boundedness. -/
lemma abs_A_le
    {a : ℕ → ℝ} (ha : BoundedByOne a) (N : ℕ) :
    |A a N| ≤ N + 1 := by
  calc
    |A a N| ≤ ∑ n ∈ Finset.range (N + 1), |a n| := by
      unfold A
      simpa using abs_sum_le_sum_abs (fun n => a n)
    _ ≤ ∑ _n ∈ Finset.range (N + 1), (1 : ℝ) := by
      refine Finset.sum_le_sum ?_
      intro n hn
      exact ha n
    _ = N + 1 := by
      simp

/-- Prefix sums vary by at most the interval length. -/
lemma abs_A_sub_le
    {a : ℕ → ℝ} (ha : BoundedByOne a) {u v : ℕ} (huv : u ≤ v) :
    |A a v - A a u| ≤ ((v - u : ℕ) : ℝ) := by
  simpa [B_eq_A_sub, Nat.add_sub_of_le huv] using abs_B_le ha u (v - u)

/-- Telescoping a progression of consecutive short blocks. -/
lemma sum_B_progression
    (a : ℕ → ℝ) (x H m : ℕ) :
    ∑ j ∈ Finset.range m, B a (x + j * H) H = A a (x + m * H) - A a x := by
  induction m with
  | zero =>
      simp
  | succ m hm =>
      rw [Finset.sum_range_succ, hm, B_eq_A_sub]
      have hstep : x + m * H + H = x + (m + 1) * H := by
        rw [Nat.succ_mul]
        omega
      rw [hstep]
      ring

/-- Markov-style bad-set estimate from the short-block energy bound. -/
theorem badSet_bound
    {a : ℕ → ℝ} {X H : ℕ} {τ η : ℝ}
    (hτ : 0 ≤ τ)
    (hE : E a X H ≤ η * X * H^2) :
    ((badSet a X H τ).card : ℝ) * (τ^2 * H^2) ≤ η * X * H^2 := by
  classical
  let s := badSet a X H τ
  have hs_threshold :
      ((s.card : ℝ) * (τ^2 * H^2)) ≤ ∑ x ∈ s, (B a x H)^2 := by
    calc
      ((s.card : ℝ) * (τ^2 * H^2)) = ∑ _x ∈ s, (τ^2 * H^2) := by
        simp [s]
      _ ≤ ∑ x ∈ s, (B a x H)^2 := by
        refine Finset.sum_le_sum ?_
        intro x hx
        have hx' : τ * H < |B a x H| := by
          exact (Finset.mem_filter.mp hx).2
        have hτH : 0 ≤ τ * (H : ℝ) := by
          positivity
        have habs_lt : |τ * (H : ℝ)| < |B a x H| := by
          simpa [abs_of_nonneg hτH] using hx'
        have habs_lt' : |τ * (H : ℝ)| < |(|B a x H|)| := by
          simpa [abs_abs] using habs_lt
        have hsq_lt : (τ * (H : ℝ))^2 < |B a x H|^2 := (sq_lt_sq).2 habs_lt' 
        calc
          τ^2 * (H : ℝ)^2 = (τ * (H : ℝ))^2 := by ring
          _ ≤ |B a x H|^2 := le_of_lt hsq_lt
          _ = (B a x H)^2 := by rw [sq_abs]
  have hs_sub : ∑ x ∈ s, (B a x H)^2 ≤ E a X H := by
    dsimp [s, badSet, E]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (by intro x hx hxnot; exact sq_nonneg (B a x H))
  change ((s.card : ℝ) * (τ^2 * (H : ℝ)^2)) ≤ η * (X : ℝ) * (H : ℝ)^2
  exact le_trans hs_threshold (le_trans hs_sub hE)

/-- The residue fibers partition the bad set. -/
lemma badSetResidue_card_sum
    {a : ℕ → ℝ} {X H : ℕ} {τ : ℝ}
    (hH : 1 ≤ H) :
    ∑ r ∈ Finset.range H, (badSetResidue a X H τ r).card = (badSet a X H τ).card := by
  classical
  calc
    ∑ r ∈ Finset.range H, (badSetResidue a X H τ r).card
        = ∑ r ∈ Finset.range H,
            ∑ x ∈ badSet a X H τ, if (x - X) % H = r then 1 else 0 := by
            refine Finset.sum_congr rfl ?_
            intro r hr
            simpa [badSetResidue] using
              (Finset.card_filter (fun x => (x - X) % H = r) (badSet a X H τ))
    _ = ∑ x ∈ badSet a X H τ,
          ∑ r ∈ Finset.range H, if (x - X) % H = r then 1 else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ x ∈ badSet a X H τ, (1 : ℕ) := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          have hH0 : 0 < H := lt_of_lt_of_le Nat.zero_lt_one hH
          have hmod : (x - X) % H < H := Nat.mod_lt _ hH0
          rw [Finset.sum_eq_single ((x - X) % H)]
          · simp
          · intro r hr hne
            have hne' : ¬ (x - X) % H = r := by
              intro hEq
              exact hne hEq.symm
            simp [hne']
          · intro hnotin
            exfalso
            exact hnotin (by simpa using hmod)
    _ = (badSet a X H τ).card := by
          symm
          exact Finset.card_eq_sum_ones _

/-- Some residue class carries at most the average number of bad starting points. -/
lemma exists_badSetResidue_card_le_average
    {a : ℕ → ℝ} {X H : ℕ} {τ : ℝ}
    (hH : 1 ≤ H) :
    ∃ r < H, ((badSetResidue a X H τ r).card : ℝ) ≤ ((badSet a X H τ).card : ℝ) / H := by
  classical
  have hsum_nat := badSetResidue_card_sum (a := a) (X := X) (H := H) (τ := τ) hH
  have hsum :
      ∑ r ∈ Finset.range H, ((badSetResidue a X H τ r).card : ℝ)
        = ((badSet a X H τ).card : ℝ) := by
    have hcast := congrArg (Nat.castAddMonoidHom ℝ) hsum_nat
    simpa [map_sum] using hcast
  by_contra h
  push_neg at h
  have hHnat : 0 < H := lt_of_lt_of_le Nat.zero_lt_one hH
  have hz : 0 ∈ Finset.range H := by
    simpa using hHnat
  have hsum_lt :
      ∑ r ∈ Finset.range H, (((badSet a X H τ).card : ℝ) / H)
        < ∑ r ∈ Finset.range H, ((badSetResidue a X H τ r).card : ℝ) := by
    refine Finset.sum_lt_sum ?_ ?_
    · intro r hr
      exact le_of_lt (h r (by simpa using hr))
    · exact ⟨0, hz, h 0 (by simpa using hz)⟩
  have hconst :
      ∑ r ∈ Finset.range H, (((badSet a X H τ).card : ℝ) / H)
        = ((badSet a X H τ).card : ℝ) := by
    have hHne : (H : ℝ) ≠ 0 := by positivity
    calc
      ∑ r ∈ Finset.range H, (((badSet a X H τ).card : ℝ) / H)
          = (H : ℝ) * (((badSet a X H τ).card : ℝ) / H) := by simp
      _ = ((badSet a X H τ).card : ℝ) := by
          field_simp [hHne]
  rw [hconst, hsum] at hsum_lt
  exact lt_irrefl _ hsum_lt

/--
The chosen-residue-class part of the critical short-block argument.

The hypothesis bounds the number of bad blocks in each relevant prefix of the chosen arithmetic
progression. The relevance condition `r + mH ≤ X` is exactly what is needed to ensure that the
first `m` blocks remain inside the dyadic window `[X,2X]`.
-/
theorem progression_quantitative
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    {X H r : ℕ}
    (hH : 1 ≤ H)
    (hr : r < H)
    {τ β : ℝ}
    (hτ0 : 0 ≤ τ)
    (hτ1 : τ ≤ 1)
    (hβ : 0 ≤ β)
    (hbad : ∀ m : ℕ, r + m * H ≤ X → ((badBlocksOnProgression a X H τ r m).card : ℝ) ≤ β) :
    ∀ N ∈ Finset.Icc X (2 * X),
      |A a N - A a X| ≤ τ * X + β * H + 2 * H := by
  intro N hN
  let x0 : ℕ := X + r
  by_cases hx0 : x0 ≤ N
  · let d : ℕ := N - x0
    let m : ℕ := d / H
    let s : ℕ := d % H
    have hdecomp : N = x0 + m * H + s := by
      dsimp [d, m, s]
      calc
        N = x0 + (N - x0) := by omega
        _ = x0 + ((N - x0) / H * H + (N - x0) % H) := by rw [Nat.div_add_mod']
        _ = x0 + (N - x0) / H * H + (N - x0) % H := by ring
    have hm_window : r + m * H ≤ X := by
      have hNle : N ≤ 2 * X := (Finset.mem_Icc.mp hN).2
      dsimp [x0] at hdecomp ⊢
      omega
    have hm_mul_le_X : m * H ≤ X := by
      omega
    let f : ℕ → ℝ := fun j => B a (progressionStart X H r j) H
    let sbad : Finset ℕ := badBlocksOnProgression a X H τ r m
    let sgood : Finset ℕ := (Finset.range m).filter (fun j => ¬ τ * H < |f j|)
    have hsum_split :
        ∑ j ∈ Finset.range m, f j = ∑ j ∈ sbad, f j + ∑ j ∈ sgood, f j := by
      dsimp [sbad, sgood, badBlocksOnProgression, f]
      simpa using
        (Finset.sum_filter_add_sum_filter_not (s := Finset.range m)
          (f := fun j => B a (progressionStart X H r j) H)
          (p := fun j => τ * H < |B a (progressionStart X H r j) H|)).symm
    have hsbad_card : (sbad.card : ℝ) ≤ β := hbad m hm_window
    have hsbad_bound : |∑ j ∈ sbad, f j| ≤ β * H := by
      have hH0 : (0 : ℝ) ≤ H := by positivity
      have h1 : |∑ j ∈ sbad, f j| ≤ (sbad.card : ℝ) * H := by
        refine abs_sum_le_card_mul_bound sbad f hH0 ?_
        intro j hj
        exact abs_B_le ha _ H
      have h2 : (sbad.card : ℝ) * H ≤ β * H := by
        nlinarith
      exact le_trans h1 h2
    have hsgood_card : sgood.card ≤ m := by
      dsimp [sgood]
      simpa using Finset.card_le_card
        (Finset.filter_subset (fun j => ¬ τ * H < |f j|) (Finset.range m))
    have hsgood_bound : |∑ j ∈ sgood, f j| ≤ τ * X := by
      have hτH0 : 0 ≤ τ * H := by
        positivity
      have h1 : |∑ j ∈ sgood, f j| ≤ (sgood.card : ℝ) * (τ * H) := by
        refine abs_sum_le_card_mul_bound sgood f hτH0 ?_
        intro j hj
        exact le_of_not_gt ((Finset.mem_filter.mp hj).2)
      have hcard_cast : (sgood.card : ℝ) ≤ m := by
        exact_mod_cast hsgood_card
      have hmHX : (m : ℝ) * H ≤ X := by
        exact_mod_cast hm_mul_le_X
      have h2 : (sgood.card : ℝ) * (τ * H) ≤ τ * X := by
        nlinarith
      exact le_trans h1 h2
    have hmiddle : |A a (x0 + m * H) - A a x0| ≤ τ * X + β * H := by
      calc
        |A a (x0 + m * H) - A a x0| = |∑ j ∈ Finset.range m, f j| := by
          have hsum_prog : ∑ j ∈ Finset.range m, f j = A a (x0 + m * H) - A a x0 := by
            dsimp [f, progressionStart, x0]
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
              (sum_B_progression a (X + r) H m)
          rw [← hsum_prog]
        _ = |∑ j ∈ sbad, f j + ∑ j ∈ sgood, f j| := by rw [hsum_split]
        _ ≤ |∑ j ∈ sbad, f j| + |∑ j ∈ sgood, f j| := by
          simpa using abs_add (∑ j ∈ sbad, f j) (∑ j ∈ sgood, f j)
        _ ≤ β * H + τ * X := by
          exact add_le_add hsbad_bound hsgood_bound
        _ = τ * X + β * H := by ring
    have htail : |A a N - A a (x0 + m * H)| ≤ H := by
      have hx0m_le_N : x0 + m * H ≤ N := by
        omega
      have h1 : |A a N - A a (x0 + m * H)| ≤ ((N - (x0 + m * H) : ℕ) : ℝ) :=
        abs_A_sub_le ha hx0m_le_N
      have h2 : N - (x0 + m * H) ≤ H := by
        have hHpos : 0 < H := Nat.succ_le_iff.mp hH
        have hslt : s < H := Nat.mod_lt _ hHpos
        have hNsub : N - (x0 + m * H) = s := by omega
        rw [hNsub]
        exact le_of_lt hslt
      exact le_trans h1 (by exact_mod_cast h2)
    have hinit : |A a x0 - A a X| ≤ H := by
      have hXx0 : X ≤ x0 := by
        dsimp [x0]
        omega
      have h1 : |A a x0 - A a X| ≤ ((x0 - X : ℕ) : ℝ) := abs_A_sub_le ha hXx0
      have h2 : x0 - X ≤ H := by
        dsimp [x0]
        omega
      exact le_trans h1 (by exact_mod_cast h2)
    calc
      |A a N - A a X|
          = |(A a N - A a (x0 + m * H))
              + (A a (x0 + m * H) - A a x0)
              + (A a x0 - A a X)| := by
                ring_nf
      _ ≤ |A a N - A a (x0 + m * H)|
            + |A a (x0 + m * H) - A a x0|
            + |A a x0 - A a X| := by
              have hfirst := abs_add (A a N - A a (x0 + m * H)) (A a (x0 + m * H) - A a x0)
              have hsecond :=
                abs_add
                  ((A a N - A a (x0 + m * H)) + (A a (x0 + m * H) - A a x0))
                  (A a x0 - A a X)
              nlinarith
      _ ≤ H + (τ * X + β * H) + H := by
            gcongr
      _ = τ * X + β * H + 2 * H := by ring
  · have hXN : X ≤ N := (Finset.mem_Icc.mp hN).1
    have h1 : |A a N - A a X| ≤ ((N - X : ℕ) : ℝ) := abs_A_sub_le ha hXN
    have h2 : N - X ≤ H := by
      dsimp [x0] at hx0
      omega
    have hrhs : H ≤ τ * X + β * H + 2 * H := by
      nlinarith
    exact le_trans h1 (le_trans (by exact_mod_cast h2) hrhs)

/--
Quantitative residue-class decomposition behind the critical short-block criterion.

This is the paper's short-block estimate on one dyadic window, with the bad-set averaging and the
arithmetic-progression decomposition fully formalized.
-/
theorem short_block_quantitative
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    {X H : ℕ}
    (hH : 1 ≤ H)
    {η τ : ℝ}
    (hτ : 0 < τ)
    (hτ1 : τ ≤ 1)
    (hE : E a X H ≤ η * X * H^2) :
    ∃ r < H,
      ∀ N ∈ Finset.Icc X (2 * X),
        |A a N - A a X| ≤ τ * X + η * X / τ^2 + 2 * H := by
  classical
  have hbadset := badSet_bound (a := a) (X := X) (H := H) (τ := τ) (η := η) hτ.le hE
  rcases exists_badSetResidue_card_le_average (a := a) (X := X) (H := H) (τ := τ) hH with
    ⟨r, hr, hres_avg⟩
  let β : ℝ := ((badSet a X H τ).card : ℝ) / H
  have hβ : 0 ≤ β := by
    dsimp [β]
    positivity
  have hbadcard : ((badSet a X H τ).card : ℝ) ≤ η * X / τ^2 := by
    have hHsq_pos : 0 < (H : ℝ)^2 := by positivity
    have hmain : ((badSet a X H τ).card : ℝ) * τ^2 ≤ η * X := by
      nlinarith [hbadset, hHsq_pos]
    have hτsq : 0 < τ^2 := by positivity
    exact (le_div_iff hτsq).2 hmain
  have hprefix :
      ∀ m : ℕ, r + m * H ≤ X → ((badBlocksOnProgression a X H τ r m).card : ℝ) ≤ β := by
    intro m hm
    let s := badBlocksOnProgression a X H τ r m
    let f : ℕ → ℕ := progressionStart X H r
    have hf_inj : Function.Injective f := by
      intro j₁ j₂ hEq
      dsimp [f, progressionStart] at hEq
      have hHpos : 0 < H := Nat.succ_le_iff.mp hH
      have hmul : j₁ * H = j₂ * H := by omega
      exact Nat.mul_right_cancel hHpos hmul
    have himage_subset : s.image f ⊆ badSetResidue a X H τ r := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨j, hj, rfl⟩
      have hjlt : j < m := by
        exact Finset.mem_range.mp ((Finset.mem_filter.mp hj).1)
      have hjbad : τ * H < |B a (progressionStart X H r j) H| := by
        exact (Finset.mem_filter.mp hj).2
      have hIcc : progressionStart X H r j ∈ Finset.Icc X (2 * X - H) := by
        refine Finset.mem_Icc.mpr ?_
        constructor
        · dsimp [progressionStart]
          omega
        · have hjsucc_le_m : j + 1 ≤ m := Nat.succ_le_of_lt hjlt
          have hmul_le : (j + 1) * H ≤ m * H := Nat.mul_le_mul_right H hjsucc_le_m
          have hupper_aux : r + (j + 1) * H ≤ X := le_trans (Nat.add_le_add_left hmul_le r) hm
          have hupper_aux' : r + j * H + H ≤ X := by
            have hsucc : (j + 1) * H = j * H + H := by rw [Nat.succ_mul]
            rw [hsucc] at hupper_aux
            simpa [Nat.add_assoc] using hupper_aux
          have hupper_add : progressionStart X H r j + H ≤ 2 * X := by
            dsimp [progressionStart]
            omega
          exact Nat.le_sub_of_add_le hupper_add
      have hbadmem : progressionStart X H r j ∈ badSet a X H τ := by
        exact Finset.mem_filter.mpr ⟨hIcc, hjbad⟩
      have hmod : (progressionStart X H r j - X) % H = r := by
        have hsub : progressionStart X H r j - X = r + j * H := by
          dsimp [progressionStart]
          omega
        rw [hsub, Nat.add_mod, Nat.mul_mod_left, Nat.mod_eq_of_lt hr]
        simpa [Nat.mod_eq_of_lt hr]
      exact Finset.mem_filter.mpr ⟨hbadmem, hmod⟩
    have hcard_image : (s.image f).card = s.card := by
      simpa [f] using Finset.card_image_of_injective s hf_inj
    have hcard_nat : s.card ≤ (badSetResidue a X H τ r).card := by
      rw [← hcard_image]
      exact Finset.card_le_card himage_subset
    have hcard_real : (s.card : ℝ) ≤ (badSetResidue a X H τ r).card := by
      exact_mod_cast hcard_nat
    exact le_trans hcard_real hres_avg
  have hprog := progression_quantitative
      (a := a) ha (X := X) (H := H) (r := r) hH hr
      (τ := τ) (β := β) hτ.le hτ1 hβ hprefix
  refine ⟨r, hr, ?_⟩
  intro N hN
  have hβH : β * H ≤ η * X / τ^2 := by
    have hHne : (H : ℝ) ≠ 0 := by positivity
    have hβeq : β * H = ((badSet a X H τ).card : ℝ) := by
      dsimp [β]
      field_simp [hHne]
    nlinarith [hβeq, hbadcard]
  have hmain := hprog N hN
  have hfinal : τ * X + β * H + 2 * H ≤ τ * X + η * X / τ^2 + 2 * H := by
    nlinarith
  exact le_trans hmain hfinal

lemma criticalScale_one_le {X : ℕ} (hX : 1 ≤ X) :
    1 ≤ criticalScale X := by
  unfold criticalScale
  exact Nat.succ_le_of_lt (Nat.sqrt_pos.2 hX)

lemma criticalScale_le_div_of_sq_le {X q : ℕ} (hq : 1 ≤ q) (hqX : q^2 ≤ X) :
    criticalScale X ≤ X / q := by
  unfold criticalScale
  have hs : q ≤ Nat.sqrt X := by
    exact Nat.le_sqrt.2 (by simpa [pow_two] using hqX)
  exact (Nat.le_div_iff_mul_le hq).2 <| by
    calc
      Nat.sqrt X * q ≤ Nat.sqrt X * Nat.sqrt X := Nat.mul_le_mul_left _ hs
      _ ≤ X := by simpa [pow_two] using Nat.sq_sqrt_le X

/-- The critical scale `⌊X^{1/2}⌋` is sublinear. -/
theorem criticalScale_sublinear : ScaleSublinear criticalScale := by
  intro ε hε
  rcases exists_nat_gt ((8 : ℝ) / ε) with ⟨q, hqgt⟩
  have hqpos_real : (0 : ℝ) < q := by
    have hpos : (0 : ℝ) < 8 / ε := by positivity
    nlinarith
  have hq : 1 ≤ q := by
    exact Nat.succ_le_of_lt (Nat.cast_pos.mp hqpos_real)
  refine ⟨q^2, ?_⟩
  intro X hX
  have hdiv_nat : criticalScale X ≤ X / q :=
    criticalScale_le_div_of_sq_le hq (by simpa using hX)
  have hdiv_real : (criticalScale X : ℝ) ≤ (X : ℝ) / q := by
    have hdiv_cast : (criticalScale X : ℝ) ≤ ((X / q : ℕ) : ℝ) := by exact_mod_cast hdiv_nat
    have hdiv_mul : ((X / q : ℕ) : ℝ) * (q : ℝ) ≤ (X : ℝ) := by
      exact_mod_cast Nat.div_mul_le_self X q
    have hdiv_floor : ((X / q : ℕ) : ℝ) ≤ (X : ℝ) / q := (le_div_iff hqpos_real).2 hdiv_mul
    exact le_trans hdiv_cast hdiv_floor
  have hmain : (8 : ℝ) ≤ ε * q := by
    have hmul := mul_lt_mul_of_pos_left hqgt hε
    have hleft : ε * (8 / ε) = (8 : ℝ) := by field_simp [ne_of_gt hε]
    nlinarith [hmul, hleft]
  have hX0 : (0 : ℝ) ≤ X := by positivity
  have hq0 : (0 : ℝ) < q := by exact hqpos_real
  have hsmall : (X : ℝ) / q ≤ (ε / 8) * X := by
    have hone_div : (1 : ℝ) / q ≤ ε / 8 := by
      have h8q : (8 : ℝ) / q ≤ ε := (div_le_iff₀ hq0).2 hmain
      have hmul := mul_le_mul_of_nonneg_right h8q (by norm_num : (0 : ℝ) ≤ 1 / 8)
      have hleft : ((8 : ℝ) / q) * (1 / 8) = (1 : ℝ) / q := by field_simp [ne_of_gt hq0]
      have hright : ε * (1 / 8) = ε / 8 := by ring
      nlinarith [hmul, hleft, hright]
    calc
      (X : ℝ) / q = ((1 : ℝ) / q) * X := by ring
      _ ≤ (ε / 8) * X := by gcongr
  have hsmall' : (X : ℝ) / q ≤ ε * X := by
    have hε8 : ε / 8 ≤ ε := by nlinarith [hε]
    exact le_trans hsmall (by gcongr)
  exact le_trans hdiv_real hsmall' 

/--
The local `[X,2X]` prefix control extracted from the short-block hypothesis at critical scale.
-/
theorem dyadicLocalControl_of_shortBlock
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    (hcrit : CriticalShortBlockHyp a)
    (hscale : ScaleSublinear criticalScale) :
    DyadicLocalControl a := by
  intro ε hε
  let ε₀ : ℝ := min ε 1
  have hε₀pos : 0 < ε₀ := by
    dsimp [ε₀]
    exact lt_min hε zero_lt_one
  have hε₀leε : ε₀ ≤ ε := by
    dsimp [ε₀]
    exact min_le_left _ _
  have hε₀le1 : ε₀ ≤ 1 := by
    dsimp [ε₀]
    exact min_le_right _ _
  let τ : ℝ := ε₀ / 4
  have hτ : 0 < τ := by
    dsimp [τ]
    positivity
  have hτ1 : τ ≤ 1 := by
    dsimp [τ]
    nlinarith
  let η : ℝ := τ^2 * ε₀ / 4
  have hη : 0 < η := by
    dsimp [η]
    positivity
  rcases hcrit η hη with ⟨X₁, hX₁⟩
  rcases hscale (ε₀ / 8) (by positivity) with ⟨X₂, hX₂⟩
  refine ⟨max X₁ (max X₂ 1), ?_⟩
  intro X N hX hN
  have hX₁le : X₁ ≤ X := by
    exact le_trans (le_max_left _ _) hX
  have hX₂le : X₂ ≤ X := by
    have hright : max X₂ 1 ≤ X := le_trans (le_max_right X₁ (max X₂ 1)) hX
    exact le_trans (le_max_left X₂ 1) hright
  have hXone : 1 ≤ X := by
    have hright : max X₂ 1 ≤ X := le_trans (le_max_right X₁ (max X₂ 1)) hX
    exact le_trans (le_max_right X₂ 1) hright
  have hH : 1 ≤ criticalScale X := criticalScale_one_le hXone
  have hE : E a X (criticalScale X) ≤ η * X * (criticalScale X)^2 := hX₁ hX₁le
  rcases short_block_quantitative (a := a) ha (X := X) (H := criticalScale X) hH hτ hτ1 hE with
    ⟨r, hr, hblock⟩
  have hscaleX : (criticalScale X : ℝ) ≤ (ε₀ / 8) * X := hX₂ hX₂le
  have hηterm : η * X / τ^2 = (ε₀ / 4) * X := by
    have hτsq : τ^2 ≠ 0 := by positivity
    dsimp [η]
    field_simp [hτsq]
  have hmain := hblock N hN
  have hfinal : τ * X + η * X / τ^2 + 2 * criticalScale X ≤ ε * X := by
    have hscale2 : 2 * (criticalScale X : ℝ) ≤ (ε₀ / 4) * X := by
      nlinarith [hscaleX]
    dsimp [τ] at hηterm ⊢
    rw [hηterm]
    nlinarith [hε₀leε]
  exact le_trans hmain hfinal

/--
Recursive-halving upgrade from local dyadic-window control to the full `o(N)` prefix estimate.
-/
theorem prefixLittleO_of_localControl
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    (hloc : DyadicLocalControl a) :
    PrefixLittleO a := by
  intro ε hε
  rcases hloc (ε / 4) (by positivity) with ⟨X₀, hX₀⟩
  let M : ℕ := max (2 * X₀) 3
  let C : ℝ := M + 1
  have hglobal : ∀ N : ℕ, |A a N| ≤ C + (ε / 2) * N := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
    by_cases hNM : N ≤ M
    · have hA : |A a N| ≤ N + 1 := abs_A_le ha N
      have hsmall : (N : ℝ) + 1 ≤ C := by
        dsimp [C]
        exact_mod_cast Nat.add_le_add_right hNM 1
      nlinarith
    · have hMN : M < N := lt_of_not_ge hNM
      let X : ℕ := (N + 1) / 2
      have hXlt : X < N := by
        dsimp [X]
        omega
      have hX₀le : X₀ ≤ X := by
        dsimp [M, X] at hMN ⊢
        omega
      have hmem : N ∈ Finset.Icc X (2 * X) := by
        dsimp [X]
        exact Finset.mem_Icc.mpr (by omega)
      have hstep : |A a N - A a X| ≤ (ε / 4) * X := hX₀ hX₀le hmem
      have hprev : |A a X| ≤ C + (ε / 2) * X := ih X hXlt
      have hXle : (X : ℝ) ≤ ((N : ℝ) + 1) / 2 := by
        have hmul : 2 * X ≤ N + 1 := by
          dsimp [X]
          exact Nat.mul_div_le (N + 1) 2
        have hmul_real : (2 : ℝ) * X ≤ (N : ℝ) + 1 := by exact_mod_cast hmul
        nlinarith
      have hNge : 3 ≤ N := by
        have hMge : 3 ≤ M := by
          dsimp [M]
          exact le_max_right _ _
        omega
      calc
        |A a N| = |(A a N - A a X) + A a X| := by ring_nf
        _ ≤ |A a N - A a X| + |A a X| := by
          simpa using abs_add (A a N - A a X) (A a X)
        _ ≤ (ε / 4) * X + (C + (ε / 2) * X) := by
          gcongr
        _ = C + (3 * ε / 4) * X := by ring
        _ ≤ C + (ε / 2) * N := by
          have hcoef_nonneg : 0 ≤ 3 * ε / 4 := by positivity
          have hXbound : (3 * ε / 4) * (X : ℝ) ≤ (3 * ε / 4) * (((N : ℝ) + 1) / 2) := by
            exact mul_le_mul_of_nonneg_left hXle hcoef_nonneg
          have hNge_real : (3 : ℝ) ≤ N := by exact_mod_cast hNge
          have htarget_aux : (3 * ε / 4) * (((N : ℝ) + 1) / 2) ≤ (ε / 2) * N := by
            nlinarith [hNge_real, hε]
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_left (le_trans hXbound htarget_aux) C
  rcases exists_nat_gt (2 * C / ε) with ⟨N₁, hN₁⟩
  refine ⟨max M N₁, ?_⟩
  intro N hN
  have hbound := hglobal N
  have hN₁le : N₁ ≤ N := le_trans (le_max_right _ _) hN
  have hCsmall : C ≤ (ε / 2) * N := by
    have hNreal : (N₁ : ℝ) ≤ N := by exact_mod_cast hN₁le
    have hCsmall₁ : C < (ε / 2) * N₁ := by
      have hmul := mul_lt_mul_of_pos_right hN₁ (by positivity : (0 : ℝ) < ε / 2)
      have hleft : (2 * C / ε) * (ε / 2) = C := by
        field_simp [ne_of_gt hε]
      nlinarith [hmul, hleft]
    have hmono : (ε / 2) * (N₁ : ℝ) ≤ (ε / 2) * N := by
      gcongr
    exact le_of_lt (lt_of_lt_of_le hCsmall₁ hmono)
  calc
    |A a N| ≤ C + (ε / 2) * N := hbound
    _ ≤ (ε / 2) * N + (ε / 2) * N := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right hCsmall ((ε / 2) * (N : ℝ))
    _ = ε * N := by ring

/--
Section 2 main theorem: critical short-block control at scale `H = ⌊X^{1/2}⌋` implies
`A(N) = o(N)`.
-/
theorem critical_short_block_criterion
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    (hcrit : CriticalShortBlockHyp a) :
    PrefixLittleO a := by
  have hloc : DyadicLocalControl a :=
    dyadicLocalControl_of_shortBlock (a := a) ha hcrit criticalScale_sublinear
  exact prefixLittleO_of_localControl (a := a) ha hloc

end ShortBlock

end FixedShiftLiouville

namespace FixedShiftLiouville

/-! ## Section 3: energy profile and quartic correlations -/

section EnergyProfile

/-- Quartic correlation sum on the dyadic window `(X,2X]`. -/
def P (a : ℕ → ℝ) (X t : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc (X + 1) (2 * X - t), a n * a (n + t)

/-- Cesàro partial sums of the quartic family, indexed from shift `1`. -/
def C (a : ℕ → ℝ) (X M : ℕ) : ℝ :=
  ∑ t ∈ Finset.range M, P a X (t + 1)

/-- The weighted quartic combination appearing in the exact energy profile. -/
def weightedPairs (a : ℕ → ℝ) (X M : ℕ) : ℝ :=
  ∑ t ∈ Finset.range M, ((M - t : ℕ) : ℝ) * P a X (t + 1)

/-- On the dyadic window `(X,2X]`, the sequence takes values in `{±1}`. -/
def SquareOneOnWindow (a : ℕ → ℝ) (X : ℕ) : Prop :=
  1 ≤ X ∧ ∀ n ∈ Finset.Icc (X + 1) (2 * X), (a n)^2 = 1

/-- Eventually the sequence takes values in `{±1}` on each dyadic window. -/
def EventuallySquareOne (a : ℕ → ℝ) : Prop :=
  ∃ X₀ : ℕ, ∀ ⦃X : ℕ⦄, X₀ ≤ X → SquareOneOnWindow a X

/-- Section 3, Proposition 3.1, in a local quantitative form. -/
def ExactEnergyProfile (a : ℕ → ℝ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ X M : ℕ, M ≤ X → SquareOneOnWindow a X →
    |E a X (M + 1) - ((((M + 1) * X : ℕ)) : ℝ) - 2 * weightedPairs a X M|
      ≤ K * (M + 1 : ℝ)^3

/-- Section 3, Corollary 3.2, in a local quantitative form. -/
def DiscreteDerivativeProfile (a : ℕ → ℝ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ X M : ℕ, M ≤ X → SquareOneOnWindow a X →
    |(E a X (M + 1) - E a X M) - X - 2 * C a X M| ≤ K * (M : ℝ)^2

lemma A_succ (a : ℕ → ℝ) (N : ℕ) :
    A a (N + 1) = A a N + a (N + 1) := by
  unfold A
  rw [Finset.sum_range_succ]

lemma B_succ (a : ℕ → ℝ) (x M : ℕ) :
    B a x (M + 1) = B a x M + a (x + M + 1) := by
  rw [B_eq_A_sub, B_eq_A_sub]
  have h : x + (M + 1) = x + M + 1 := by omega
  rw [h, A_succ]
  ring

lemma B_eq_sum_range (a : ℕ → ℝ) (x M : ℕ) :
    B a x M = ∑ i ∈ Finset.range M, a (x + 1 + i) := by
  unfold B
  rw [Finset.sum_Icc_eq_sum_range]
  have hlen : x + (M + 1) - (x + 1) = M := by omega
  simp [hlen, Nat.add_assoc]

lemma B_eq_sum_range_rev (a : ℕ → ℝ) (x M : ℕ) :
    B a x M = ∑ t ∈ Finset.range M, a (x + M - t) := by
  rw [B_eq_sum_range]
  calc
    ∑ i ∈ Finset.range M, a (x + 1 + i)
        = ∑ i ∈ Finset.range M, a (x + 1 + (M - 1 - i)) := by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            (Finset.sum_range_reflect (f := fun i => a (x + 1 + i)) M).symm
    _ = ∑ t ∈ Finset.range M, a (x + M - t) := by
          refine Finset.sum_congr rfl ?_
          intro t ht
          congr 1
          have htlt : t < M := Finset.mem_range.mp ht
          omega

lemma E_eq_sum_range (a : ℕ → ℝ) {X M : ℕ} (hM : M ≤ X) :
    E a X M = ∑ i ∈ Finset.range (X - M + 1), (B a (X + i) M)^2 := by
  unfold E
  rw [Finset.sum_Icc_eq_sum_range]
  have hlen : 2 * X - M + 1 - X = X - M + 1 := by omega
  simp [hlen, Nat.add_assoc]

lemma weightedPairs_zero (a : ℕ → ℝ) (X : ℕ) : weightedPairs a X 0 = 0 := by
  unfold weightedPairs
  simp

lemma weightedPairs_succ (a : ℕ → ℝ) (X M : ℕ) :
    weightedPairs a X (M + 1) = weightedPairs a X M + C a X (M + 1) := by
  unfold weightedPairs C
  rw [Finset.sum_range_succ]
  have hsum :
      ∑ t ∈ Finset.range M, (((M + 1 - t : ℕ)) : ℝ) * P a X (t + 1)
        = ∑ t ∈ Finset.range M,
            ((((M - t : ℕ)) : ℝ) * P a X (t + 1) + P a X (t + 1)) := by
    refine Finset.sum_congr rfl ?_
    intro t ht
    have htlt : t < M := Finset.mem_range.mp ht
    have hsub : M + 1 - t = (M - t) + 1 := by omega
    rw [hsub]
    norm_num [Nat.cast_add]
    ring
  rw [hsum, Finset.sum_add_distrib, Finset.sum_range_succ]
  have hlast : M + 1 - M = 1 := by omega
  rw [hlast]
  ring_nf

lemma E_one_eq_X
    {a : ℕ → ℝ} {X : ℕ}
    (hsq : SquareOneOnWindow a X) :
    E a X 1 = X := by
  have h1 : 1 ≤ X := hsq.1
  rw [E_eq_sum_range (a := a) (X := X) (M := 1) h1]
  have hXm : X - 1 + 1 = X := by omega
  rw [hXm]
  have hterm : ∀ i ∈ Finset.range X, (B a (X + i) 1)^2 = 1 := by
    intro i hi
    have hilt : i < X := Finset.mem_range.mp hi
    have hmem : X + i + 1 ∈ Finset.Icc (X + 1) (2 * X) := by
      exact Finset.mem_Icc.mpr (by constructor <;> omega)
    have hs : (a (X + i + 1))^2 = 1 := hsq.2 _ hmem
    rw [B_eq_sum_range]
    simp [hs]
  calc
    ∑ i ∈ Finset.range X, (B a (X + i) 1)^2 = ∑ _i ∈ Finset.range X, (1 : ℝ) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      exact hterm i hi
    _ = X := by simp

lemma pair_term_abs_le_one
    {a : ℕ → ℝ} (ha : BoundedByOne a) (n t : ℕ) :
    |a n * a (n + t)| ≤ 1 := by
  calc
    |a n * a (n + t)| = |a n| * |a (n + t)| := by rw [abs_mul]
    _ ≤ 1 * 1 := by gcongr <;> exact ha _
    _ = 1 := by ring

/-- The exact cross-term sum arising in the discrete derivative expansion. -/
def crossTail (a : ℕ → ℝ) (X M t : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc (X + M - t) (2 * X - t - 1), a n * a (n + (t + 1))

lemma crossTail_subsum
    (a : ℕ → ℝ) {X M t : ℕ} (ht : t < M) (hM : M ≤ X) :
    crossTail a X M t
      = ∑ i ∈ Finset.range (X - M), a (X + i + M - t) * a (X + i + M + 1) := by
  unfold crossTail
  rw [Finset.sum_Icc_eq_sum_range]
  have hlen : (2 * X - t - 1) + 1 - (X + M - t) = X - M := by omega
  rw [hlen]
  refine Finset.sum_congr rfl ?_
  intro i hi
  congr 2 <;> omega

lemma crossTail_approx
    {a : ℕ → ℝ} (ha : BoundedByOne a)
    {X M t : ℕ} (ht : t < M) (hM : M ≤ X) :
    |crossTail a X M t - P a X (t + 1)| ≤ M := by
  classical
  have hsubset : Finset.Icc (X + M - t) (2 * X - t - 1) ⊆ Finset.Icc (X + 1) (2 * X - (t + 1)) := by
    intro n hn
    simp at hn ⊢
    omega
  let missing : Finset ℕ := (Finset.Icc (X + 1) (2 * X - (t + 1))).filter (fun n => n < X + M - t)
  have hsplit :
      P a X (t + 1) =
        ∑ n ∈ missing, a n * a (n + (t + 1)) + crossTail a X M t := by
    unfold P crossTail missing
    let big := Finset.Icc (X + 1) (2 * X - (t + 1))
    let p : ℕ → Prop := fun n => X + M - t ≤ n
    have hset : Finset.Icc (X + M - t) (2 * X - t - 1) = big.filter p := by
      ext n
      simp [big, p]
      omega
    have hmiss : big.filter (fun n => ¬ p n) = big.filter (fun n => n < X + M - t) := by
      ext n
      simp [big, p]
      omega
    rw [hset]
    have hsum := (Finset.sum_filter_add_sum_filter_not (s := big)
      (f := fun n => a n * a (n + (t + 1))) (p := p)).symm
    rw [← hmiss]
    simpa [add_comm] using hsum
  have hmissing_card : missing.card ≤ M := by
    have hsubmiss : missing ⊆ Finset.Icc (X + 1) (X + M) := by
      intro n hn
      simp [missing] at hn ⊢
      omega
    calc
      missing.card ≤ (Finset.Icc (X + 1) (X + M)).card := Finset.card_le_card hsubmiss
      _ = M := by simp
  have hmissing_bound : |∑ n ∈ missing, a n * a (n + (t + 1))| ≤ M := by
    have h1 : |∑ n ∈ missing, a n * a (n + (t + 1))| ≤ (missing.card : ℝ) * 1 := by
      refine abs_sum_le_card_mul_bound missing (fun n => a n * a (n + (t + 1))) (by positivity) ?_
      intro n hn
      simpa using pair_term_abs_le_one ha n (t + 1)
    have h2 : (missing.card : ℝ) * 1 ≤ M := by
      have hmreal : (missing.card : ℝ) ≤ M := by exact_mod_cast hmissing_card
      nlinarith
    exact le_trans h1 h2
  have hmain : crossTail a X M t - P a X (t + 1) = - ∑ n ∈ missing, a n * a (n + (t + 1)) := by
    rw [hsplit]
    ring
  rw [hmain]
  simpa using hmissing_bound

lemma abs_P_le_X
    {a : ℕ → ℝ} (ha : BoundedByOne a) (X t : ℕ) :
    |P a X t| ≤ X := by
  have h1 : |P a X t| ≤ ((Finset.Icc (X + 1) (2 * X - t)).card : ℝ) * 1 := by
    unfold P
    refine abs_sum_le_card_mul_bound (Finset.Icc (X + 1) (2 * X - t))
      (fun n => a n * a (n + t)) (by positivity) ?_
    intro n hn
    simpa using pair_term_abs_le_one ha n t
  have hcard : (Finset.Icc (X + 1) (2 * X - t)).card ≤ X := by
    have hsub : Finset.Icc (X + 1) (2 * X - t) ⊆ Finset.Icc (X + 1) (2 * X) := by
      intro n hn
      simp at hn ⊢
      omega
    calc
      (Finset.Icc (X + 1) (2 * X - t)).card ≤ (Finset.Icc (X + 1) (2 * X)).card :=
        Finset.card_le_card hsub
      _ = X := by
        simp
        omega
  have hcardR : (((Finset.Icc (X + 1) (2 * X - t)).card : ℕ) : ℝ) ≤ X := by
    exact_mod_cast hcard
  nlinarith

lemma abs_C_le_X_sq
    {a : ℕ → ℝ} (ha : BoundedByOne a) (X M : ℕ) (hM : M ≤ X) :
    |C a X M| ≤ (X : ℝ)^2 := by
  have h1 : |C a X M| ≤ (M : ℝ) * X := by
    unfold C
    have hsum : |∑ t ∈ Finset.range M, P a X (t + 1)| ≤ (M : ℝ) * X := by
      have h := abs_sum_le_card_mul_bound (Finset.range M)
        (fun t => P a X (t + 1)) (by positivity : (0 : ℝ) ≤ X) ?_
      · simpa using h
      · intro t ht
        exact abs_P_le_X ha X (t + 1)
    simpa using hsum
  have hMX : (M : ℝ) ≤ X := by exact_mod_cast hM
  have hXnonneg : 0 ≤ (X : ℝ) := by positivity
  nlinarith

lemma E_endpoint_succ_eq_zero
    (a : ℕ → ℝ) {X : ℕ} (hX : 1 ≤ X) :
    E a X (X + 1) = 0 := by
  unfold E
  have hlt : 2 * X - (X + 1) < X := by omega
  rw [Finset.Icc_eq_empty_of_lt hlt]
  simp

lemma abs_E_diag_le_sq
    {a : ℕ → ℝ} (ha : BoundedByOne a) (X : ℕ) :
    |E a X X| ≤ (X : ℝ)^2 := by
  rw [E_eq_sum_range (a := a) (X := X) (M := X) le_rfl]
  simp
  have hB : |B a X X| ≤ X := abs_B_le ha X X
  rw [← sq_abs]
  nlinarith [abs_nonneg (B a X X)]

lemma discrete_derivative_endpoint_bound
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    {X : ℕ}
    (hX : 1 ≤ X)
    (hsq : SquareOneOnWindow a X) :
    |(E a X (X + 1) - E a X X) - X - 2 * C a X X|
      ≤ 6 * (X : ℝ)^2 := by
  have hE0 : E a X (X + 1) = 0 := E_endpoint_succ_eq_zero a hX
  have hE : |E a X X| ≤ (X : ℝ)^2 := abs_E_diag_le_sq ha X
  have hC : |C a X X| ≤ (X : ℝ)^2 := abs_C_le_X_sq ha X X le_rfl
  have hXsq : (X : ℝ) ≤ (X : ℝ)^2 := by
    have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX
    nlinarith [sq_nonneg ((X : ℝ) - 1)]
  rw [hE0]
  calc
    |(0 - E a X X) - X - 2 * C a X X|
        = |-(E a X X) - X + -(2 * C a X X)| := by ring_nf
    _ ≤ |E a X X| + (X : ℝ) + 2 * |C a X X| := by
          have h1 := abs_add (-(E a X X) - X) (-(2 * C a X X))
          have h2 := abs_add (-(E a X X)) (-(X : ℝ))
          have h2' : |-(E a X X) - X| ≤ |E a X X| + (X : ℝ) := by
            simpa [sub_eq_add_neg, abs_neg] using h2
          have h1' : |-(E a X X) - X + -(2 * C a X X)|
              ≤ |-(E a X X) - X| + |-(2 * C a X X)| := by
            simpa [sub_eq_add_neg] using h1
          have h2abs : |-(2 * C a X X)| = 2 * |C a X X| := by
            rw [abs_neg, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
          nlinarith
    _ ≤ (X : ℝ)^2 + (X : ℝ)^2 + 2 * (X : ℝ)^2 := by
          nlinarith
    _ ≤ 6 * (X : ℝ)^2 := by
          nlinarith [sq_nonneg (X : ℝ)]

/-- A clean quantitative discrete-derivative bound. -/
theorem discrete_derivative_of_energy_profile
    {a : ℕ → ℝ}
    (ha : BoundedByOne a) :
    DiscreteDerivativeProfile a := by
  refine ⟨6, by positivity, ?_⟩
  intro X M hM hsq
  by_cases hM0 : M = 0
  · subst M
    have hE0 : E a X 0 = 0 := by
      unfold E B
      simp
    rw [E_one_eq_X hsq, hE0]
    unfold C
    simp
  · by_cases hMX : M = X
    · subst M
      have hX : 1 ≤ X := hsq.1
      exact discrete_derivative_endpoint_bound ha hX hsq
    · have hMpos : 1 ≤ M := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hM0)
      have hM1 : M + 1 ≤ X := Nat.succ_le_of_lt (lt_of_le_of_ne hM hMX)
      have hMs : M - 1 < M := Nat.pred_lt hM0
      have hEM1 : E a X (M + 1) = ∑ i ∈ Finset.range (X - M), (B a (X + i) (M + 1))^2 := by
        rw [E_eq_sum_range (a := a) (X := X) (M := M + 1) hM1]
        congr
        omega
      have hEM : E a X M =
          (∑ i ∈ Finset.range (X - M), (B a (X + i) M)^2) + (B a (2 * X - M) M)^2 := by
        rw [E_eq_sum_range (a := a) (X := X) (M := M) hM]
        have : X - M + 1 = (X - M) + 1 := by omega
        rw [this, Finset.sum_range_succ]
        have hlastx : X + (X - M) = 2 * X - M := by omega
        rw [hlastx]
      let D : ℝ := ∑ i ∈ Finset.range (X - M), (a (X + i + M + 1))^2
      let Q : ℕ → ℝ := fun t => crossTail a X M t
      have hcross_expand :
          ∑ i ∈ Finset.range (X - M), 2 * B a (X + i) M * a (X + i + M + 1)
            = 2 * ∑ t ∈ Finset.range M, Q t := by
        unfold Q
        calc
          ∑ i ∈ Finset.range (X - M), 2 * B a (X + i) M * a (X + i + M + 1)
              = ∑ i ∈ Finset.range (X - M),
                  2 * (∑ t ∈ Finset.range M, a (X + i + M - t)) * a (X + i + M + 1) := by
                    refine Finset.sum_congr rfl ?_
                    intro i hi
                    rw [B_eq_sum_range_rev]
              _ = ∑ i ∈ Finset.range (X - M),
                  ∑ t ∈ Finset.range M, 2 * (a (X + i + M - t) * a (X + i + M + 1)) := by
                    refine Finset.sum_congr rfl ?_
                    intro i hi
                    rw [mul_sum, sum_mul]
                    refine Finset.sum_congr rfl ?_
                    intro t ht
                    ring
              _ = ∑ t ∈ Finset.range M,
                  ∑ i ∈ Finset.range (X - M), 2 * (a (X + i + M - t) * a (X + i + M + 1)) := by
                    rw [Finset.sum_comm]
              _ = 2 * ∑ t ∈ Finset.range M, Q t := by
                    rw [mul_sum]
                    refine Finset.sum_congr rfl ?_
                    intro t ht
                    rw [← Finset.mul_sum]
                    rw [← crossTail_subsum (a := a) (X := X) (M := M) (t := t) (Finset.mem_range.mp ht) hM]
      have hdiag_exact : D = X - M := by
        unfold D
        have hcard : (∑ i ∈ Finset.range (X - M), (a (X + i + M + 1))^2)
            = ∑ _i ∈ Finset.range (X - M), (1 : ℝ) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              have hmem : X + i + M + 1 ∈ Finset.Icc (X + 1) (2 * X) := by
                have hilt : i < X - M := Finset.mem_range.mp hi
                exact Finset.mem_Icc.mpr (by constructor <;> omega)
              exact hsq.2 _ hmem
        rw [hcard]
        simp [Nat.cast_sub hM]
      have hdiag : |D - X| ≤ (M : ℝ) := by
        rw [hdiag_exact]
        have hdiff : (X : ℝ) - (M : ℝ) - (X : ℝ) = -(M : ℝ) := by ring
        rw [hdiff, abs_neg, abs_of_nonneg (by positivity : 0 ≤ (M : ℝ))]
      have hQapprox : ∀ t ∈ Finset.range M, |Q t - P a X (t + 1)| ≤ M := by
        intro t ht
        exact crossTail_approx ha (Finset.mem_range.mp ht) hM
      have hQsum : |∑ t ∈ Finset.range M, Q t - C a X M| ≤ (M : ℝ)^2 := by
        have h1 : |∑ t ∈ Finset.range M, (Q t - P a X (t + 1))| ≤ (M : ℝ) * M := by
          have hraw : |∑ t ∈ Finset.range M, (Q t - P a X (t + 1))| ≤ ((Finset.range M).card : ℝ) * M := by
            refine abs_sum_le_card_mul_bound (Finset.range M) (fun t => Q t - P a X (t + 1)) (by positivity : 0 ≤ (M : ℝ)) ?_
            intro t ht
            exact hQapprox t ht
          simpa using hraw
        have h2 : ∑ t ∈ Finset.range M, Q t - C a X M = ∑ t ∈ Finset.range M, (Q t - P a X (t + 1)) := by
          unfold C
          rw [Finset.sum_sub_distrib]
        calc
          |∑ t ∈ Finset.range M, Q t - C a X M|
              = |∑ t ∈ Finset.range M, (Q t - P a X (t + 1))| := by rw [h2]
          _ ≤ (M : ℝ) * M := h1
          _ = (M : ℝ)^2 := by ring
      have hlast : |(B a (2 * X - M) M)^2| ≤ (M : ℝ)^2 := by
        have h1 : |B a (2 * X - M) M| ≤ M := abs_B_le ha _ _
        rw [abs_sq, ← sq_abs]
        nlinarith [abs_nonneg (B a (2 * X - M) M)]
      have hdecomp :
          (E a X (M + 1) - E a X M) - X - 2 * C a X M
            = (2 * ∑ t ∈ Finset.range M, Q t - 2 * C a X M)
              + (D - X) - (B a (2 * X - M) M)^2 := by
        rw [hEM1, hEM]
        have hsqexpand :
            ∑ i ∈ Finset.range (X - M), (B a (X + i) (M + 1))^2
              = ∑ i ∈ Finset.range (X - M),
                  (2 * B a (X + i) M * a (X + i + M + 1) + (a (X + i + M + 1))^2 + (B a (X + i) M)^2) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                rw [B_succ]
                ring
        rw [hsqexpand]
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        unfold D
        rw [hcross_expand]
        ring
      rw [hdecomp]
      have hcross2 : |2 * ∑ t ∈ Finset.range M, Q t - 2 * C a X M| ≤ 2 * (M : ℝ)^2 := by
        have heq : 2 * ∑ t ∈ Finset.range M, Q t - 2 * C a X M
            = 2 * (∑ t ∈ Finset.range M, Q t - C a X M) := by ring
        rw [heq, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        nlinarith
      have hmain :
          |(2 * ∑ t ∈ Finset.range M, Q t - 2 * C a X M) + (D - X) - (B a (2 * X - M) M)^2|
            ≤ 2 * (M : ℝ)^2 + (M : ℝ) + (M : ℝ)^2 := by
        calc
          |(2 * ∑ t ∈ Finset.range M, Q t - 2 * C a X M) + (D - X) - (B a (2 * X - M) M)^2|
              ≤ |2 * ∑ t ∈ Finset.range M, Q t - 2 * C a X M| + |D - X| + |(B a (2 * X - M) M)^2| := by
                let A : ℝ := 2 * ∑ t ∈ Finset.range M, Q t - 2 * C a X M
                let B0 : ℝ := D - X
                let L : ℝ := (B a (2 * X - M) M)^2
                have hAB : |A + (B0 - L)| ≤ |A| + |B0 - L| := by
                  simpa using abs_add A (B0 - L)
                have hBL : |B0 - L| ≤ |B0| + |L| := by
                  simpa [sub_eq_add_neg, abs_neg] using abs_add B0 (-L)
                calc
                  |(2 * ∑ t ∈ Finset.range M, Q t - 2 * C a X M) + (D - X) - (B a (2 * X - M) M)^2|
                      = |A + (B0 - L)| := by simp [A, B0, L, sub_eq_add_neg, add_assoc]
                  _ ≤ |A| + |B0 - L| := hAB
                  _ ≤ |A| + (|B0| + |L|) := by gcongr
                  _ = |2 * ∑ t ∈ Finset.range M, Q t - 2 * C a X M| + |D - X| + |(B a (2 * X - M) M)^2| := by
                        simp [A, B0, L, add_assoc, add_comm, add_left_comm]
          _ ≤ 2 * (M : ℝ)^2 + (M : ℝ) + (M : ℝ)^2 := by
                nlinarith [hcross2, hdiag, hlast]
      have hMlin : (M : ℝ) ≤ (M : ℝ)^2 := by
        have hMposR : (1 : ℝ) ≤ M := by exact_mod_cast hMpos
        nlinarith [sq_nonneg ((M : ℝ) - 1)]
      exact le_trans hmain (by nlinarith [hMlin])

/-- The exact energy profile is obtained by summing the discrete derivative estimate. -/
theorem exact_energy_profile
    {a : ℕ → ℝ}
    (ha : BoundedByOne a) :
    ExactEnergyProfile a := by
  rcases discrete_derivative_of_energy_profile (a := a) ha with ⟨K, hK, hdisc⟩
  refine ⟨max K 1, le_trans hK (le_max_left K 1), ?_⟩
  intro X M hM hsq
  let F : ℕ → ℝ := fun m => E a X (m + 1) - ((((m + 1) * X : ℕ)) : ℝ) - 2 * weightedPairs a X m
  have hbase : F 0 = 0 := by
    unfold F
    rw [weightedPairs_zero, E_one_eq_X hsq]
    ring
  have hstep : ∀ m : ℕ, m ≤ X → |F m| ≤ (max K 1) * (m + 1 : ℝ)^3 := by
    intro m hm
    induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hm0 : m = 0
    · subst m
      rw [hbase]
      simp
    · have hmpos : 1 ≤ m := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hm0)
      have hpred : m - 1 < m := Nat.pred_lt hm0
      have hpredle : m - 1 ≤ X := by omega
      have hIH := ih (m - 1) hpred hpredle
      have hdisc' := hdisc X m hm hsq
      have hrec : F m = F (m - 1) + ((E a X (m + 1) - E a X m) - X - 2 * C a X m) := by
        have hm_sub : m - 1 + 1 = m := by omega
        have hw : weightedPairs a X m = weightedPairs a X (m - 1) + C a X m := by
          simpa [hm_sub] using (weightedPairs_succ (a := a) (X := X) (M := m - 1))
        have hcast : ((((m + 1) * X : ℕ)) : ℝ) = ((((m * X : ℕ)) : ℝ) + X) := by
          norm_num [Nat.cast_mul, Nat.cast_add, left_distrib]
          ring_nf
        unfold F
        rw [hw, hm_sub, hcast]
        ring
      rw [hrec]
      have hsum :
          |F (m - 1) + ((E a X (m + 1) - E a X m) - X - 2 * C a X m)|
            ≤ |F (m - 1)| + |(E a X (m + 1) - E a X m) - X - 2 * C a X m| := by
          simpa using abs_add (F (m - 1)) ((E a X (m + 1) - E a X m) - X - 2 * C a X m)
      have hK1 : 1 ≤ max K 1 := le_max_right _ _
      calc
        |F (m - 1) + ((E a X (m + 1) - E a X m) - X - 2 * C a X m)|
            ≤ |F (m - 1)| + |(E a X (m + 1) - E a X m) - X - 2 * C a X m| := hsum
        _ ≤ (max K 1) * (m : ℝ)^3 + (max K 1) * (m : ℝ)^2 := by
              have hpredcast : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by
                have hm_nat : m - 1 + 1 = m := by omega
                exact_mod_cast hm_nat
              have hIH' : |F (m - 1)| ≤ (max K 1) * (m : ℝ)^3 := by
                simpa [hpredcast] using hIH
              have hdiscK : |E a X (m + 1) - E a X m - ↑X - 2 * C a X m|
                  ≤ (max K 1) * (m : ℝ)^2 := by
                exact le_trans hdisc' (by nlinarith [le_max_left K 1])
              nlinarith
        _ ≤ (max K 1) * (m + 1 : ℝ)^3 := by
              have hmposR : (1 : ℝ) ≤ m := by exact_mod_cast hmpos
              nlinarith [hK1, sq_nonneg (m : ℝ)]
  have hmain := hstep M hM
  simpa [F] using hmain


/-- Epsilon-form of the uniform slope hypothesis from Corollary 3.3. -/
def UniformSlopeHyp (a : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ X₀ : ℕ, ∀ ⦃X M : ℕ⦄, X₀ ≤ X → 1 ≤ M → M ≤ criticalScale X →
    |(E a X (M + 1) - E a X M) - X| ≤ ε * X * criticalScale X

lemma weightedPairs_eq_sum_C (a : ℕ → ℝ) (X M : ℕ) :
    weightedPairs a X M = ∑ m ∈ Finset.range M, C a X (m + 1) := by
  induction M with
  | zero =>
      simp [weightedPairs_zero]
  | succ M hM =>
      rw [weightedPairs_succ, hM, Finset.sum_range_succ]

lemma weightedPairs_bound_of_C_bound
    {a : ℕ → ℝ} {X M : ℕ} {B : ℝ}
    (hB0 : 0 ≤ B)
    (hB : ∀ m ∈ Finset.range M, |C a X (m + 1)| ≤ B) :
    |weightedPairs a X M| ≤ M * B := by
  rw [weightedPairs_eq_sum_C]
  have h1 :
      |∑ m ∈ Finset.range M, C a X (m + 1)| ≤ ((Finset.range M).card : ℝ) * B := by
    refine abs_sum_le_card_mul_bound (Finset.range M) (fun m => C a X (m + 1)) hB0 ?_
    intro m hm
    exact hB m hm
  simpa using h1

lemma criticalScale_sq_le (X : ℕ) : (criticalScale X)^2 ≤ X := by
  unfold criticalScale
  exact Nat.sq_sqrt_le X

lemma criticalScale_ge_of_sq_le {X q : ℕ} (hqX : q^2 ≤ X) :
    q ≤ criticalScale X := by
  unfold criticalScale
  rw [sq] at hqX
  exact Nat.le_sqrt.2 hqX

/--
Corollary 3.3 first yields the critical short-block hypothesis at the critical scale.
-/
theorem criticalShortBlock_of_uniformSlope
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    (hsqev : EventuallySquareOne a)
    (hslope : UniformSlopeHyp a) :
    CriticalShortBlockHyp a := by
  rcases discrete_derivative_of_energy_profile (a := a) ha with ⟨Kd, hKd, hdisc⟩
  rcases exact_energy_profile (a := a) ha with ⟨Ke, hKe, hExact⟩
  intro ε hε
  let δ : ℝ := ε / 3
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  rcases hslope δ hδ with ⟨X₁, hX₁⟩
  rcases hsqev with ⟨Xsq, hsqall⟩
  rcases exists_nat_gt ((3 : ℝ) / ε) with ⟨q₁, hq₁⟩
  rcases exists_nat_gt ((3 : ℝ) * (Kd + Ke) / ε) with ⟨q₂, hq₂⟩
  let Q : ℕ := max 1 (max q₁ q₂)
  let X₂ : ℕ := Q^2
  refine ⟨max X₁ (max Xsq X₂), ?_⟩
  intro X hX
  let H : ℕ := criticalScale X
  have hX₁le : X₁ ≤ X := by
    exact le_trans (le_max_left _ _) hX
  have hXsqle : Xsq ≤ X := by
    exact le_trans (le_trans (le_max_left Xsq X₂) (le_max_right X₁ (max Xsq X₂))) hX
  have hX₂le : X₂ ≤ X := by
    exact le_trans (le_trans (le_max_right Xsq X₂) (le_max_right X₁ (max Xsq X₂))) hX
  have hQone : 1 ≤ Q := by
    dsimp [Q]
    exact le_max_left _ _
  have hQleH : Q ≤ H := by
    dsimp [H, X₂] at hX₂le ⊢
    exact criticalScale_ge_of_sq_le hX₂le
  have hHone : 1 ≤ H := le_trans hQone hQleH
  have hsq : SquareOneOnWindow a X := hsqall hXsqle
  have hHsq_nat : H^2 ≤ X := by
    dsimp [H]
    exact criticalScale_sq_le X
  have hHsq : (H : ℝ)^2 ≤ X := by
    exact_mod_cast hHsq_nat
  have hHleX : H ≤ X := by
    have hHs : H ≤ H^2 := by
      nlinarith [hHone]
    exact le_trans hHs hHsq_nat
  have hpredle : H - 1 ≤ X := by
    omega
  have hCbound :
      ∀ m ∈ Finset.range (H - 1),
        |C a X (m + 1)| ≤ (δ * X * H + Kd * H^2) / 2 := by
    intro m hm
    have hm_lt : m < H - 1 := Finset.mem_range.mp hm
    have hm1_le_H : m + 1 ≤ H := by
      omega
    have hm1_le_X : m + 1 ≤ X := le_trans hm1_le_H hHleX
    have hslope_m :
        |(E a X ((m + 1) + 1) - E a X (m + 1)) - X| ≤ δ * X * H := by
      exact hX₁ hX₁le (Nat.succ_le_succ (Nat.zero_le m)) (by simpa [H] using hm1_le_H)
    have hdisc_m :
        |(E a X ((m + 1) + 1) - E a X (m + 1)) - X - 2 * C a X (m + 1)| ≤ Kd * (H : ℝ)^2 := by
      have h0 := hdisc X (m + 1) hm1_le_X hsq
      have hm1_real : ((m + 1 : ℕ) : ℝ) ≤ H := by
        exact_mod_cast hm1_le_H
      have hsquare : ((m + 1 : ℕ) : ℝ)^2 ≤ (H : ℝ)^2 := by
        have hm1_nonneg : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by positivity
        have hH_nonneg : (0 : ℝ) ≤ (H : ℝ) := by positivity
        nlinarith [sq_nonneg ((H : ℝ) - ((m + 1 : ℕ) : ℝ))]
      exact le_trans h0 (mul_le_mul_of_nonneg_left hsquare hKd)
    have htwo :
        |(2 : ℝ) * C a X (m + 1)| ≤ δ * X * H + Kd * (H : ℝ)^2 := by
      let A0 : ℝ := (E a X ((m + 1) + 1) - E a X (m + 1)) - X
      let B0 : ℝ := (E a X ((m + 1) + 1) - E a X (m + 1)) - X - 2 * C a X (m + 1)
      have heq : (2 : ℝ) * C a X (m + 1) = A0 - B0 := by
        dsimp [A0, B0]
        ring
      calc
        |(2 : ℝ) * C a X (m + 1)| = |A0 - B0| := by rw [heq]
        _ ≤ |A0| + |B0| := by
              simpa [sub_eq_add_neg, abs_neg] using abs_add A0 (-B0)
        _ ≤ δ * X * H + Kd * (H : ℝ)^2 := by
              dsimp [A0, B0]
              exact add_le_add hslope_m hdisc_m
    have htwo' : 2 * |C a X (m + 1)| ≤ δ * X * H + Kd * (H : ℝ)^2 := by
      simpa [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] using htwo
    nlinarith
  have hB0 : 0 ≤ (δ * X * H + Kd * H^2) / 2 := by
    positivity
  have hWP :
      |weightedPairs a X (H - 1)| ≤ ((H - 1 : ℕ) : ℝ) * ((δ * X * H + Kd * (H : ℝ)^2) / 2) := by
    exact weightedPairs_bound_of_C_bound hB0 hCbound
  have hWP2 : |2 * weightedPairs a X (H - 1)| ≤ δ * X * (H : ℝ)^2 + Kd * (H : ℝ)^3 := by
    let S : ℝ := δ * X * H + Kd * (H : ℝ)^2
    have hm1le : ((H - 1 : ℕ) : ℝ) ≤ H := by
      exact_mod_cast Nat.sub_le H 1
    have hSnonneg : 0 ≤ S := by
      dsimp [S]
      positivity
    have h0 : 2 * |weightedPairs a X (H - 1)|
        ≤ 2 * ((H - 1 : ℕ) : ℝ) * (S / 2) := by
      dsimp [S]
      nlinarith
    have h1 : 2 * ((H - 1 : ℕ) : ℝ) * (S / 2)
        ≤ δ * X * (H : ℝ)^2 + Kd * (H : ℝ)^3 := by
      calc
        2 * ((H - 1 : ℕ) : ℝ) * (S / 2) = ((H - 1 : ℕ) : ℝ) * S := by ring
        _ ≤ (H : ℝ) * S := by gcongr
        _ = δ * X * (H : ℝ)^2 + Kd * (H : ℝ)^3 := by
              dsimp [S]
              ring
    have h2 : |2 * weightedPairs a X (H - 1)| = 2 * |weightedPairs a X (H - 1)| := by
      simp [abs_mul]
    rw [h2]
    exact le_trans h0 h1
  have hHpred : H - 1 + 1 = H := Nat.sub_add_cancel hHone
  have happrox0 := hExact X (H - 1) hpredle hsq
  rw [hHpred] at happrox0
  have happrox :
      |E a X H - (H : ℝ) * X - 2 * weightedPairs a X (H - 1)| ≤ Ke * (H : ℝ)^3 := by
    have hHpredR : ((H - 1 : ℕ) : ℝ) + 1 = (H : ℝ) := by
      exact_mod_cast hHpred
    simpa [Nat.cast_mul, hHpredR] using happrox0
  have happrox_upper :
      E a X H - (H : ℝ) * X - 2 * weightedPairs a X (H - 1) ≤ Ke * (H : ℝ)^3 := by
    exact (abs_le.mp happrox).2
  have hWP_upper :
      2 * weightedPairs a X (H - 1) ≤ δ * X * (H : ℝ)^2 + Kd * (H : ℝ)^3 := by
    exact (abs_le.mp hWP2).2
  have hEbound : E a X H ≤ H * X + δ * X * (H : ℝ)^2 + (Kd + Ke) * (H : ℝ)^3 := by
    nlinarith [happrox_upper, hWP_upper]
  have hQreal : (Q : ℝ) ≤ H := by
    exact_mod_cast hQleH
  have hq₁leQ : q₁ ≤ Q := by
    dsimp [Q]
    exact le_trans (le_max_left q₁ q₂) (le_max_right 1 (max q₁ q₂))
  have hq₂leQ : q₂ ≤ Q := by
    dsimp [Q]
    exact le_trans (le_max_right q₁ q₂) (le_max_right 1 (max q₁ q₂))
  have hq₁real : (q₁ : ℝ) ≤ Q := by exact_mod_cast hq₁leQ
  have hq₂real : (q₂ : ℝ) ≤ Q := by exact_mod_cast hq₂leQ
  have hHXsmall : H * X ≤ (ε / 3) * X * (H : ℝ)^2 := by
    have hHbig : (3 : ℝ) / ε < H :=
      lt_of_lt_of_le hq₁ (le_trans hq₁real hQreal)
    have heps3pos : 0 < ε / 3 := by positivity
    have hmul_lt := mul_lt_mul_of_pos_left hHbig heps3pos
    have hleft : (ε / 3) * ((3 : ℝ) / ε) = 1 := by
      field_simp [ne_of_gt hε]
    have hfactor : (1 : ℝ) ≤ (ε / 3) * H := by
      rw [hleft] at hmul_lt
      exact le_of_lt hmul_lt
    have hnonneg : 0 ≤ (X : ℝ) * H := by positivity
    have hmul := mul_le_mul_of_nonneg_right hfactor hnonneg
    calc
      (H : ℝ) * X = 1 * (X * H) := by ring
      _ ≤ ((ε / 3) * H) * (X * H) := hmul
      _ = (ε / 3) * X * (H : ℝ)^2 := by ring
  have hErrsmall : (Kd + Ke) * (H : ℝ)^3 ≤ (ε / 3) * X * (H : ℝ)^2 := by
    have hHbig : (3 : ℝ) * (Kd + Ke) / ε < H :=
      lt_of_lt_of_le hq₂ (le_trans hq₂real hQreal)
    have heps3pos : 0 < ε / 3 := by positivity
    have hmul_lt := mul_lt_mul_of_pos_left hHbig heps3pos
    have hleft : (ε / 3) * ((3 : ℝ) * (Kd + Ke) / ε) = Kd + Ke := by
      field_simp [ne_of_gt hε]
    have hcoefH : Kd + Ke ≤ (ε / 3) * H := by
      have hmul_lt' : Kd + Ke < (ε / 3) * H := by
        exact hleft ▸ hmul_lt
      exact le_of_lt hmul_lt'
    have hHnonneg : 0 ≤ (H : ℝ) := by positivity
    have hcoefH2 : (Kd + Ke) * H ≤ ((ε / 3) * H) * H :=
      mul_le_mul_of_nonneg_right hcoefH hHnonneg
    have hcoefH2' : (Kd + Ke) * H ≤ (ε / 3) * (H : ℝ)^2 := by
      convert hcoefH2 using 1 <;> ring
    have hepsnonneg : 0 ≤ ε / 3 := by positivity
    have hcoefX : (ε / 3) * (H : ℝ)^2 ≤ (ε / 3) * X := by
      exact mul_le_mul_of_nonneg_left hHsq hepsnonneg
    have hcoef : (Kd + Ke) * H ≤ (ε / 3) * X := le_trans hcoefH2' hcoefX
    have hH2nonneg : 0 ≤ (H : ℝ)^2 := sq_nonneg _
    have hmul := mul_le_mul_of_nonneg_right hcoef hH2nonneg
    calc
      (Kd + Ke) * (H : ℝ)^3 = ((Kd + Ke) * H) * (H : ℝ)^2 := by ring
      _ ≤ ((ε / 3) * X) * (H : ℝ)^2 := hmul
      _ = (ε / 3) * X * (H : ℝ)^2 := by ring
  have hfinal : E a X H ≤ ε * X * (H : ℝ)^2 := by
    dsimp [δ] at hEbound
    have hmiddle :
        (H : ℝ) * X + (ε / 3) * X * (H : ℝ)^2 + (Kd + Ke) * (H : ℝ)^3
          ≤ (ε / 3) * X * (H : ℝ)^2
            + (ε / 3) * X * (H : ℝ)^2
            + (ε / 3) * X * (H : ℝ)^2 := by
      exact add_le_add (add_le_add hHXsmall le_rfl) hErrsmall
    calc
      E a X H
          ≤ (H : ℝ) * X + (ε / 3) * X * (H : ℝ)^2 + (Kd + Ke) * (H : ℝ)^3 := hEbound
      _ ≤ (ε / 3) * X * (H : ℝ)^2
            + (ε / 3) * X * (H : ℝ)^2
            + (ε / 3) * X * (H : ℝ)^2 := hmiddle
      _ = ε * X * (H : ℝ)^2 := by ring
  simpa [H] using hfinal

/--
Corollary 3.3: a uniform small-slope bound for the discrete energy derivative
implies the Section 2 short-block criterion, hence the global prefix estimate.
-/
theorem uniform_slope_criterion
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    (hsqev : EventuallySquareOne a)
    (hslope : UniformSlopeHyp a) :
    PrefixLittleO a := by
  apply critical_short_block_criterion (a := a) ha
  exact criticalShortBlock_of_uniformSlope (a := a) ha hsqev hslope

end EnergyProfile

end FixedShiftLiouville

namespace FixedShiftLiouville

section PositiveMultiscale

/-- The positive multiscale hypothesis from Section 4, localized at the critical scale. -/
def PositiveMultiscaleHyp (a : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ X₀ : ℕ, ∀ ⦃X : ℕ⦄, X₀ ≤ X →
    ∑ M ∈ Finset.Icc 1 (criticalScale X), E a X M / (M : ℝ)^2
      ≤ ε * X * criticalScale X

/--
Abstract Fourier-to-energy bridge for Section 4.

This packages exactly the analytic estimate needed later: every discrete energy increment up to the
critical scale is controlled by the positive multiscale sum, up to the natural `O(H²)` boundary
loss that appears in the paper.
-/
def PositiveMultiscaleBridge (a : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ X M : ℕ, 1 ≤ M → M ≤ criticalScale X →
    |(E a X (M + 1) - E a X M) - X|
      ≤ C * 
          (∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2)
        + C * (criticalScale X : ℝ)^2

lemma E_nonneg (a : ℕ → ℝ) (X M : ℕ) : 0 ≤ E a X M := by
  unfold E
  positivity

lemma eventually_criticalScale_ge (q : ℕ) :
    ∃ X₀ : ℕ, ∀ ⦃X : ℕ⦄, X₀ ≤ X → q ≤ criticalScale X := by
  refine ⟨q^2, ?_⟩
  intro X hX
  exact criticalScale_ge_of_sq_le (by simpa using hX)

/--
Section 4 reduction: a positive multiscale bound together with the Fourier bridge yields the
uniform slope hypothesis from Section 3.
-/
theorem uniformSlope_of_positiveMultiscale
    {a : ℕ → ℝ}
    (hbridge : PositiveMultiscaleBridge a)
    (hmulti : PositiveMultiscaleHyp a) :
    UniformSlopeHyp a := by
  rcases hbridge with ⟨C, hC, hbridgeC⟩
  intro ε hε
  let C' : ℝ := max C 1
  have hC'pos : 0 < C' := by
    dsimp [C']
    nlinarith [le_max_right C 1]
  let η : ℝ := ε / (2 * C')
  have hη : 0 < η := by
    dsimp [η]
    positivity
  rcases hmulti η hη with ⟨X₁, hX₁⟩
  rcases exists_nat_gt ((2 * C') / ε) with ⟨q, hqgt⟩
  have hqpos_real : (0 : ℝ) < q := by
    have hthreshold_pos : (0 : ℝ) < (2 * C') / ε := by
      positivity
    exact lt_trans hthreshold_pos hqgt
  have hq : 1 ≤ q := by
    exact Nat.succ_le_of_lt (Nat.cast_pos.mp hqpos_real)
  rcases eventually_criticalScale_ge q with ⟨X₂, hX₂⟩
  refine ⟨max X₁ X₂, ?_⟩
  intro X M hX hM hMcrit
  have hX₁le : X₁ ≤ X := by
    exact le_trans (le_max_left _ _) hX
  have hX₂le : X₂ ≤ X := by
    exact le_trans (le_max_right _ _) hX
  have hsum :
      ∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2
        ≤ η * X * criticalScale X := by
    exact hX₁ hX₁le
  have hqleH : q ≤ criticalScale X := by
    exact hX₂ hX₂le
  have hqleH_real : (q : ℝ) ≤ criticalScale X := by
    exact_mod_cast hqleH
  have hHbig : (2 * C') / ε < criticalScale X := by
    exact lt_of_lt_of_le hqgt hqleH_real
  have hsum_small :
      C * (∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2)
        ≤ (ε / 2) * X * criticalScale X := by
    have hC_le : C ≤ C' := by
      dsimp [C']
      exact le_max_left _ _
    have hCη : C * η ≤ ε / 2 := by
      dsimp [η]
      have hfac_nonneg : 0 ≤ ε / (2 * C') := by positivity
      have hmul := mul_le_mul_of_nonneg_right hC_le hfac_nonneg
      have hright : C' * (ε / (2 * C')) = ε / 2 := by
        field_simp [ne_of_gt hC'pos]
      exact le_trans hmul (le_of_eq hright)
    have hXH_nonneg : 0 ≤ (X : ℝ) * criticalScale X := by positivity
    have hηbound : C * (η * X * criticalScale X) ≤ (ε / 2) * X * criticalScale X := by
      calc
        C * (η * X * criticalScale X)
            = (C * η) * ((X : ℝ) * criticalScale X) := by ring
        _ ≤ (ε / 2) * ((X : ℝ) * criticalScale X) :=
            mul_le_mul_of_nonneg_right hCη hXH_nonneg
        _ = (ε / 2) * X * criticalScale X := by ring
    exact le_trans (mul_le_mul_of_nonneg_left hsum hC) hηbound
  have herror_small : C * (criticalScale X : ℝ)^2 ≤ (ε / 2) * X * criticalScale X := by
    have hC_le : C ≤ C' := by
      dsimp [C']
      exact le_max_left _ _
    have hCprime_small : C' ≤ (ε / 2) * criticalScale X := by
      have hmul := mul_lt_mul_of_pos_left hHbig (show 0 < ε / 2 by positivity)
      have hleft : (ε / 2) * (2 * C' / ε) = C' := by
        field_simp [ne_of_gt hε]
      have hlt : C' < (ε / 2) * criticalScale X := by
        exact hleft ▸ hmul
      exact le_of_lt hlt
    have hC_small : C ≤ (ε / 2) * criticalScale X := le_trans hC_le hCprime_small
    have hHsq : (criticalScale X : ℝ)^2 ≤ X := by
      exact_mod_cast criticalScale_sq_le X
    have hH2_nonneg : 0 ≤ (criticalScale X : ℝ)^2 := sq_nonneg _
    have hstep1 : C * (criticalScale X : ℝ)^2
        ≤ ((ε / 2) * criticalScale X) * (criticalScale X : ℝ)^2 :=
      mul_le_mul_of_nonneg_right hC_small hH2_nonneg
    have hfac_nonneg : 0 ≤ (ε / 2) * criticalScale X := by positivity
    have hstep2 : ((ε / 2) * criticalScale X) * (criticalScale X : ℝ)^2
        ≤ ((ε / 2) * criticalScale X) * X :=
      mul_le_mul_of_nonneg_left hHsq hfac_nonneg
    calc
      C * (criticalScale X : ℝ)^2
          ≤ ((ε / 2) * criticalScale X) * (criticalScale X : ℝ)^2 := hstep1
      _ ≤ ((ε / 2) * criticalScale X) * X := hstep2
      _ = (ε / 2) * X * criticalScale X := by ring
  have hmain := hbridgeC X M hM hMcrit
  calc
    |(E a X (M + 1) - E a X M) - X|
        ≤ C * (∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2)
            + C * (criticalScale X : ℝ)^2 := hmain
    _ ≤ (ε / 2) * X * criticalScale X + (ε / 2) * X * criticalScale X := by
          exact add_le_add hsum_small herror_small
    _ ≤ ε * X * criticalScale X := by
          ring_nf
          exact le_rfl

/--
Theorem 4.3 in clean reduction form: once the positive multiscale bound has been converted into
uniform slope control, Section 3 and then Section 2 finish the argument.
-/
theorem positive_multiscale_criterion
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    (hsqev : EventuallySquareOne a)
    (hbridge : PositiveMultiscaleBridge a)
    (hmulti : PositiveMultiscaleHyp a) :
    PrefixLittleO a := by
  apply uniform_slope_criterion (a := a) ha hsqev
  exact uniformSlope_of_positiveMultiscale hbridge hmulti

end PositiveMultiscale

end FixedShiftLiouville

namespace FixedShiftLiouville

section PositiveMultiscaleRefined

/-- The diagonal mass on the dyadic window `(X,2X]`. -/
def diagonalMass (a : ℕ → ℝ) (X : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc (X + 1) (2 * X), (a n)^2

/-- On a window where `a(n)^2 = 1`, the diagonal mass is exactly the window length. -/
lemma diagonalMass_eq_X_of_squareOne
    {a : ℕ → ℝ} {X : ℕ}
    (hsq : SquareOneOnWindow a X) :
    diagonalMass a X = X := by
  unfold diagonalMass
  calc
    ∑ n ∈ Finset.Icc (X + 1) (2 * X), (a n)^2
        = ∑ _n ∈ Finset.Icc (X + 1) (2 * X), (1 : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            exact hsq.2 n hn
    _ = X := by
        simp
        omega

/--
Section 4 in a form closer to the paper: the discrete derivative is controlled relative to the
local diagonal Fourier mass, rather than relative to `X` directly.
-/
def DirichletOscillationBridge (a : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ X M : ℕ, 1 ≤ M → M ≤ criticalScale X →
    |(E a X (M + 1) - E a X M) - diagonalMass a X|
      ≤ C * (∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2)
        + C * (criticalScale X : ℝ)^2

/--
Refined Section 4 reduction: once the oscillatory increment is absorbed by the positive
multiscale quantity, the eventual `a(n)^2 = 1` hypothesis identifies the main term with `X`,
recovering the uniform-slope hypothesis of Section 3.
-/
theorem uniformSlope_of_dirichletOscillation
    {a : ℕ → ℝ}
    (hsqev : EventuallySquareOne a)
    (hosc : DirichletOscillationBridge a)
    (hmulti : PositiveMultiscaleHyp a) :
    UniformSlopeHyp a := by
  rcases hosc with ⟨C, hC, hoscC⟩
  rcases hsqev with ⟨Xsq, hsqall⟩
  intro ε hε
  let C' : ℝ := max C 1
  have hC'pos : 0 < C' := by
    dsimp [C']
    nlinarith [le_max_right C 1]
  let η : ℝ := ε / (2 * C')
  have hη : 0 < η := by
    dsimp [η]
    positivity
  rcases hmulti η hη with ⟨X₁, hX₁⟩
  rcases exists_nat_gt ((2 * C') / ε) with ⟨q, hqgt⟩
  have hqpos_real : (0 : ℝ) < q := by
    have hthreshold_pos : (0 : ℝ) < (2 * C') / ε := by
      positivity
    exact lt_trans hthreshold_pos hqgt
  have hq : 1 ≤ q := by
    exact Nat.succ_le_of_lt (Nat.cast_pos.mp hqpos_real)
  rcases eventually_criticalScale_ge q with ⟨X₂, hX₂⟩
  refine ⟨max Xsq (max X₁ X₂), ?_⟩
  intro X M hX hM hMcrit
  have hXsqle : Xsq ≤ X := by
    exact le_trans (le_max_left _ _) hX
  have hX₁le : X₁ ≤ X := by
    exact le_trans (le_trans (le_max_left X₁ X₂) (le_max_right Xsq (max X₁ X₂))) hX
  have hX₂le : X₂ ≤ X := by
    exact le_trans (le_trans (le_max_right X₁ X₂) (le_max_right Xsq (max X₁ X₂))) hX
  have hsq : SquareOneOnWindow a X := hsqall hXsqle
  have hmass : diagonalMass a X = X := diagonalMass_eq_X_of_squareOne hsq
  have hsum :
      ∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2
        ≤ η * X * criticalScale X := by
    exact hX₁ hX₁le
  have hqleH : q ≤ criticalScale X := by
    exact hX₂ hX₂le
  have hqleH_real : (q : ℝ) ≤ criticalScale X := by
    exact_mod_cast hqleH
  have hHbig : (2 * C') / ε < criticalScale X := by
    exact lt_of_lt_of_le hqgt hqleH_real
  have hsum_small :
      C * (∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2)
        ≤ (ε / 2) * X * criticalScale X := by
    have hC_le : C ≤ C' := by
      dsimp [C']
      exact le_max_left _ _
    have hCη : C * η ≤ ε / 2 := by
      dsimp [η]
      have hfac_nonneg : 0 ≤ ε / (2 * C') := by positivity
      have hmul := mul_le_mul_of_nonneg_right hC_le hfac_nonneg
      have hright : C' * (ε / (2 * C')) = ε / 2 := by
        field_simp [ne_of_gt hC'pos]
      exact le_trans hmul (le_of_eq hright)
    have hXH_nonneg : 0 ≤ (X : ℝ) * criticalScale X := by positivity
    have hηbound : C * (η * X * criticalScale X) ≤ (ε / 2) * X * criticalScale X := by
      calc
        C * (η * X * criticalScale X)
            = (C * η) * ((X : ℝ) * criticalScale X) := by ring
        _ ≤ (ε / 2) * ((X : ℝ) * criticalScale X) :=
            mul_le_mul_of_nonneg_right hCη hXH_nonneg
        _ = (ε / 2) * X * criticalScale X := by ring
    exact le_trans (mul_le_mul_of_nonneg_left hsum hC) hηbound
  have herror_small : C * (criticalScale X : ℝ)^2 ≤ (ε / 2) * X * criticalScale X := by
    have hC_le : C ≤ C' := by
      dsimp [C']
      exact le_max_left _ _
    have hCprime_small : C' ≤ (ε / 2) * criticalScale X := by
      have hmul := mul_lt_mul_of_pos_left hHbig (show 0 < ε / 2 by positivity)
      have hleft : (ε / 2) * (2 * C' / ε) = C' := by
        field_simp [ne_of_gt hε]
      have hlt : C' < (ε / 2) * criticalScale X := by
        exact hleft ▸ hmul
      exact le_of_lt hlt
    have hC_small : C ≤ (ε / 2) * criticalScale X := le_trans hC_le hCprime_small
    have hHsq : (criticalScale X : ℝ)^2 ≤ X := by
      exact_mod_cast criticalScale_sq_le X
    have hH2_nonneg : 0 ≤ (criticalScale X : ℝ)^2 := sq_nonneg _
    have hstep1 : C * (criticalScale X : ℝ)^2
        ≤ ((ε / 2) * criticalScale X) * (criticalScale X : ℝ)^2 :=
      mul_le_mul_of_nonneg_right hC_small hH2_nonneg
    have hfac_nonneg : 0 ≤ (ε / 2) * criticalScale X := by positivity
    have hstep2 : ((ε / 2) * criticalScale X) * (criticalScale X : ℝ)^2
        ≤ ((ε / 2) * criticalScale X) * X :=
      mul_le_mul_of_nonneg_left hHsq hfac_nonneg
    calc
      C * (criticalScale X : ℝ)^2
          ≤ ((ε / 2) * criticalScale X) * (criticalScale X : ℝ)^2 := hstep1
      _ ≤ ((ε / 2) * criticalScale X) * X := hstep2
      _ = (ε / 2) * X * criticalScale X := by ring
  have hmain := hoscC X M hM hMcrit
  rw [hmass] at hmain
  calc
    |(E a X (M + 1) - E a X M) - X|
        ≤ C * (∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2)
            + C * (criticalScale X : ℝ)^2 := hmain
    _ ≤ (ε / 2) * X * criticalScale X + (ε / 2) * X * criticalScale X := by
          exact add_le_add hsum_small herror_small
    _ ≤ ε * X * criticalScale X := by
          ring_nf
          exact le_rfl

/--
Refined Theorem 4.3: the positive multiscale hypothesis, together with the more faithful
Dirichlet-oscillation bridge, implies the global prefix cancellation conclusion.
-/
theorem positive_multiscale_criterion_refined
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    (hsqev : EventuallySquareOne a)
    (hosc : DirichletOscillationBridge a)
    (hmulti : PositiveMultiscaleHyp a) :
    PrefixLittleO a := by
  apply uniform_slope_criterion (a := a) ha hsqev
  exact uniformSlope_of_dirichletOscillation hsqev hosc hmulti

end PositiveMultiscaleRefined

end FixedShiftLiouville


namespace FixedShiftLiouville

section FourierMainTerms

/--
The symmetric Fejér-side main term written in coefficient language:
diagonal contribution plus twice the positive-shift weighted correlations.
-/
def fejerMainTerm (a : ℕ → ℝ) (X M : ℕ) : ℝ :=
  (((M + 1 : ℕ) : ℝ) * diagonalMass a X) + 2 * weightedPairs a X M

/--
The symmetric Dirichlet-side main term written in coefficient language:
diagonal contribution plus twice the positive-shift Cesàro correlation sum.
-/
def dirichletMainTerm (a : ℕ → ℝ) (X M : ℕ) : ℝ :=
  diagonalMass a X + 2 * C a X M

/-- The Fejér-side main terms telescope to the Dirichlet-side main term. -/
lemma fejerMainTerm_succ_sub (a : ℕ → ℝ) (X M : ℕ) :
    fejerMainTerm a X (M + 1) - fejerMainTerm a X M = dirichletMainTerm a X (M + 1) := by
  unfold fejerMainTerm dirichletMainTerm
  rw [weightedPairs_succ]
  norm_num [Nat.cast_add]
  ring

/-- On a `±1` window, the Dirichlet-side diagonal term is exactly `X`. -/
lemma dirichletMainTerm_eq_X_plus_twoC_of_squareOne
    {a : ℕ → ℝ} {X M : ℕ}
    (hsq : SquareOneOnWindow a X) :
    dirichletMainTerm a X M = X + 2 * C a X M := by
  unfold dirichletMainTerm
  rw [diagonalMass_eq_X_of_squareOne hsq]

/-- A paper-shaped Fejér representation, but phrased in coefficient language. -/
def FejerRepresentation (a : ℕ → ℝ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ X M : ℕ, M ≤ X → SquareOneOnWindow a X →
    |E a X (M + 1) - fejerMainTerm a X M| ≤ K * (M + 1 : ℝ)^3

/-- A paper-shaped Dirichlet increment representation, phrased in coefficient language. -/
def DirichletIncrementRepresentation (a : ℕ → ℝ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ X M : ℕ, M ≤ X → SquareOneOnWindow a X →
    |(E a X (M + 1) - E a X M) - dirichletMainTerm a X M| ≤ K * (M : ℝ)^2

/--
Section 3 already provides the coefficient-form Fejér representation once the window is
square-one.
-/
theorem fejer_representation
    {a : ℕ → ℝ}
    (ha : BoundedByOne a) :
    FejerRepresentation a := by
  rcases exact_energy_profile (a := a) ha with ⟨K, hK, hprof⟩
  refine ⟨K, hK, ?_⟩
  intro X M hM hsq
  have hmain := hprof X M hM hsq
  have hmass : diagonalMass a X = X := diagonalMass_eq_X_of_squareOne hsq
  have hcast : ((((M + 1) * X : ℕ)) : ℝ) = (((M + 1 : ℕ) : ℝ) * (X : ℝ)) := by
    exact_mod_cast (show (M + 1) * X = (M + 1) * X by rfl)
  rw [hcast, ← hmass] at hmain
  have hshape :
      E a X (M + 1) - fejerMainTerm a X M
        = E a X (M + 1) - (((M + 1 : ℕ) : ℝ) * diagonalMass a X)
            - 2 * weightedPairs a X M := by
    unfold fejerMainTerm
    ring
  rw [hshape]
  simpa using hmain

/--
Section 3 also provides the coefficient-form Dirichlet increment representation.
-/
theorem dirichlet_increment_representation
    {a : ℕ → ℝ}
    (ha : BoundedByOne a) :
    DirichletIncrementRepresentation a := by
  rcases discrete_derivative_of_energy_profile (a := a) ha with ⟨K, hK, hdisc⟩
  refine ⟨K, hK, ?_⟩
  intro X M hM hsq
  have hmain := hdisc X M hM hsq
  rw [dirichletMainTerm_eq_X_plus_twoC_of_squareOne hsq]
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hmain

/-- The critical scale never exceeds the ambient scale. -/
lemma criticalScale_le_self (X : ℕ) : criticalScale X ≤ X := by
  by_cases hX : X = 0
  · subst hX
    simp [criticalScale]
  · have hX1 : 1 ≤ X := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hX)
    have hH1 : 1 ≤ criticalScale X := criticalScale_one_le hX1
    have hHs : (criticalScale X)^2 ≤ X := criticalScale_sq_le X
    have hHsq : criticalScale X ≤ (criticalScale X)^2 := by
      calc
        criticalScale X = criticalScale X * 1 := by rw [Nat.mul_one]
        _ ≤ criticalScale X * criticalScale X := Nat.mul_le_mul_left _ hH1
        _ = (criticalScale X)^2 := by rw [pow_two]
    exact le_trans hHsq hHs

/--
The remaining Section 4 input after the coefficient-form Dirichlet representation is isolated as
a control of the Dirichlet main term relative to the diagonal mass.
-/
def DirichletMainTermControl (a : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ X M : ℕ, 1 ≤ M → M ≤ criticalScale X →
    |dirichletMainTerm a X M - diagonalMass a X|
      ≤ C * (∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2)
        + C * (criticalScale X : ℝ)^2

/--
Once the coefficient-form Dirichlet representation is combined with a direct control of the
Dirichlet main term and the positive multiscale hypothesis, one recovers the uniform-slope
criterion of Section 3.
-/
theorem uniformSlope_of_dirichletMainTermControl
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    (hsqev : EventuallySquareOne a)
    (hctrl : DirichletMainTermControl a)
    (hmulti : PositiveMultiscaleHyp a) :
    UniformSlopeHyp a := by
  rcases dirichlet_increment_representation (a := a) ha with ⟨K, hK, hrepr⟩
  rcases hctrl with ⟨C, hC, hctrlC⟩
  rcases hsqev with ⟨Xsq, hsqall⟩
  intro ε hε
  let C' : ℝ := max (C + K) 1
  have hC'pos : 0 < C' := by
    dsimp [C']
    nlinarith [le_max_right (C + K) 1]
  let η : ℝ := ε / (2 * C')
  have hη : 0 < η := by
    dsimp [η]
    positivity
  rcases hmulti η hη with ⟨X₁, hX₁⟩
  rcases exists_nat_gt ((4 * C') / ε) with ⟨q, hqgt⟩
  have hqpos_real : (0 : ℝ) < q := by
    have hthreshold_pos : (0 : ℝ) < (4 * C') / ε := by
      positivity
    exact lt_trans hthreshold_pos hqgt
  have hq : 1 ≤ q := by
    exact Nat.succ_le_of_lt (Nat.cast_pos.mp hqpos_real)
  rcases eventually_criticalScale_ge q with ⟨X₂, hX₂⟩
  refine ⟨max Xsq (max X₁ X₂), ?_⟩
  intro X M hX hM hMcrit
  have hXsqle : Xsq ≤ X := by
    exact le_trans (le_max_left _ _) hX
  have hX₁le : X₁ ≤ X := by
    exact le_trans (le_trans (le_max_left X₁ X₂) (le_max_right Xsq (max X₁ X₂))) hX
  have hX₂le : X₂ ≤ X := by
    exact le_trans (le_trans (le_max_right X₁ X₂) (le_max_right Xsq (max X₁ X₂))) hX
  have hsq : SquareOneOnWindow a X := hsqall hXsqle
  have hmass : diagonalMass a X = X := diagonalMass_eq_X_of_squareOne hsq
  have hsum :
      ∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2
        ≤ η * X * criticalScale X := by
    exact hX₁ hX₁le
  have hqleH : q ≤ criticalScale X := by
    exact hX₂ hX₂le
  have hqleH_real : (q : ℝ) ≤ criticalScale X := by
    exact_mod_cast hqleH
  have hHbig : (4 * C') / ε < criticalScale X := by
    nlinarith [hqgt, hqleH_real]
  have hsum_nonneg :
      0 ≤ ∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2 := by
    refine Finset.sum_nonneg ?_
    intro j hj
    exact div_nonneg (E_nonneg a X j) (sq_nonneg (j : ℝ))
  have hsum_small :
      C' * (∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2)
        ≤ (ε / 2) * X * criticalScale X := by
    have hη_eq : C' * (η * X * criticalScale X) ≤ (ε / 2) * X * criticalScale X := by
      have hη_eq_eq : C' * (η * X * criticalScale X) = (ε / 2) * X * criticalScale X := by
        dsimp [η]
        have hcoef : C' * (ε / (2 * C')) = ε / 2 := by
          field_simp [ne_of_gt hC'pos]
        calc
          C' * (ε / (2 * C') * X * criticalScale X)
              = (C' * (ε / (2 * C'))) * ((X : ℝ) * criticalScale X) := by ring
          _ = (ε / 2) * X * criticalScale X := by rw [hcoef]; ring
      exact le_of_eq hη_eq_eq
    exact le_trans (mul_le_mul_of_nonneg_left hsum (le_of_lt hC'pos)) hη_eq
  have herror_small :
      2 * C' * (criticalScale X : ℝ)^2 ≤ (ε / 2) * X * criticalScale X := by
    have hC_small : 2 * C' ≤ (ε / 2) * criticalScale X := by
      have hmul := mul_lt_mul_of_pos_left hHbig (show 0 < ε / 2 by positivity)
      have hleft : (ε / 2) * (4 * C' / ε) = 2 * C' := by
        field_simp [ne_of_gt hε]
        ring
      exact le_of_lt (hleft ▸ hmul)
    have hHsq : (criticalScale X : ℝ)^2 ≤ X := by
      exact_mod_cast criticalScale_sq_le X
    have hH2nonneg : 0 ≤ (criticalScale X : ℝ)^2 := sq_nonneg _
    have hfacnonneg : 0 ≤ (ε / 2) * criticalScale X := by positivity
    calc
      2 * C' * (criticalScale X : ℝ)^2
          ≤ ((ε / 2) * criticalScale X) * (criticalScale X : ℝ)^2 :=
            mul_le_mul_of_nonneg_right hC_small hH2nonneg
      _ ≤ ((ε / 2) * criticalScale X) * X :=
            mul_le_mul_of_nonneg_left hHsq hfacnonneg
      _ = (ε / 2) * X * criticalScale X := by ring
  have hctrl_main :
      |dirichletMainTerm a X M - diagonalMass a X|
        ≤ C' * (∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2)
          + C' * (criticalScale X : ℝ)^2 := by
    have hmain := hctrlC X M hM hMcrit
    have hC_le : C ≤ C' := by
      dsimp [C']
      have h1 : C ≤ C + K := by nlinarith [hK]
      exact le_trans h1 (le_max_left _ _)
    calc
      |dirichletMainTerm a X M - diagonalMass a X|
          ≤ C * (∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2)
            + C * (criticalScale X : ℝ)^2 := hmain
      _ ≤ C' * (∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2)
            + C' * (criticalScale X : ℝ)^2 := by
            exact add_le_add
              (mul_le_mul_of_nonneg_right hC_le hsum_nonneg)
              (mul_le_mul_of_nonneg_right hC_le (sq_nonneg (criticalScale X : ℝ)))
  have hMX : M ≤ X := by
    exact le_trans hMcrit (criticalScale_le_self X)
  have hrepr_main :
      |(E a X (M + 1) - E a X M) - dirichletMainTerm a X M|
        ≤ C' * (criticalScale X : ℝ)^2 := by
    have hmain := hrepr X M hMX hsq
    have hK_le : K ≤ C' := by
      dsimp [C']
      have h1 : K ≤ C + K := by nlinarith [hC]
      exact le_trans h1 (le_max_left _ _)
    have hMcrit_real : (M : ℝ) ≤ criticalScale X := by
      exact_mod_cast hMcrit
    calc
      |(E a X (M + 1) - E a X M) - dirichletMainTerm a X M|
          ≤ K * (M : ℝ)^2 := hmain
      _ ≤ K * (criticalScale X : ℝ)^2 := by
          have hsquare : (M : ℝ)^2 ≤ (criticalScale X : ℝ)^2 := by
            have hmul := mul_le_mul hMcrit_real hMcrit_real (by positivity : 0 ≤ (M : ℝ)) (by positivity : 0 ≤ (criticalScale X : ℝ))
            simpa [pow_two] using hmul
          exact mul_le_mul_of_nonneg_left hsquare hK
      _ ≤ C' * (criticalScale X : ℝ)^2 := by
          exact mul_le_mul_of_nonneg_right hK_le (sq_nonneg (criticalScale X : ℝ))
  have htotal :
      C' * (criticalScale X : ℝ)^2
          + (C' * (∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2)
              + C' * (criticalScale X : ℝ)^2)
        ≤ ε * X * criticalScale X := by
    calc
      C' * (criticalScale X : ℝ)^2
          + (C' * (∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2)
              + C' * (criticalScale X : ℝ)^2)
          = C' * (∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2)
              + 2 * C' * (criticalScale X : ℝ)^2 := by ring
      _ ≤ (ε / 2) * X * criticalScale X + (ε / 2) * X * criticalScale X := by
            exact add_le_add hsum_small herror_small
      _ ≤ ε * X * criticalScale X := by
            ring_nf
            exact le_rfl
  calc
    |(E a X (M + 1) - E a X M) - X|
        = |((E a X (M + 1) - E a X M) - dirichletMainTerm a X M)
            + (dirichletMainTerm a X M - diagonalMass a X)| := by
              rw [hmass]
              congr 1
              ring
    _ ≤ |(E a X (M + 1) - E a X M) - dirichletMainTerm a X M|
          + |dirichletMainTerm a X M - diagonalMass a X| := by
            exact abs_add _ _
    _ ≤ C' * (criticalScale X : ℝ)^2
          + (C' * (∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2)
              + C' * (criticalScale X : ℝ)^2) := by
            exact add_le_add hrepr_main hctrl_main
    _ ≤ ε * X * criticalScale X := htotal

/--
A polished Section 4 criterion: it is enough to control the Dirichlet main term itself, since the
representation error is already supplied by the completed Section 3 formalization.
-/
theorem positive_multiscale_criterion_mainTerm
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    (hsqev : EventuallySquareOne a)
    (hctrl : DirichletMainTermControl a)
    (hmulti : PositiveMultiscaleHyp a) :
    PrefixLittleO a := by
  apply uniform_slope_criterion (a := a) ha hsqev
  exact uniformSlope_of_dirichletMainTermControl ha hsqev hctrl hmulti

end FourierMainTerms


section PositiveDominationCoefficient

/--
A coefficient-level version of the positive domination lemma from Section 4.

It directly bounds the Dirichlet-side oscillatory main term by a positive multiscale sum of
Fejér-side main terms. The indexing `j - 1` is chosen so that the Section 3 Fejér representation,
which controls `E a X j`, plugs in without an index shift.
-/
def PositiveDominationCoefficient (a : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ X L : ℕ, 1 ≤ L → L ≤ criticalScale X →
    |dirichletMainTerm a X L - diagonalMass a X|
      ≤ C * (∑ j ∈ Finset.Icc 1 (criticalScale X), fejerMainTerm a X (j - 1) / (j : ℝ)^2)

/-- A crude bound for the sum of the first `H` positive integers over `Icc 1 H`. -/
lemma sum_Icc_cast_id_le_sq (H : ℕ) :
    ∑ j ∈ Finset.Icc 1 H, (j : ℝ) ≤ (H : ℝ)^2 := by
  calc
    ∑ j ∈ Finset.Icc 1 H, (j : ℝ) ≤ ∑ j ∈ Finset.Icc 1 H, (H : ℝ) := by
      refine Finset.sum_le_sum ?_
      intro j hj
      exact_mod_cast (Finset.mem_Icc.mp hj).2
    _ = (H : ℝ) * H := by
      rw [Finset.sum_Icc_eq_sum_range]
      have hlen : H + 1 - 1 = H := by omega
      rw [hlen]
      simp [Finset.sum_const, Finset.card_range]
    _ = (H : ℝ)^2 := by ring

/--
Section 4 in paper order: coefficient-level positive domination, together with the completed
Section 3 Fejér and Dirichlet representations, implies the uniform slope hypothesis.
-/
theorem uniformSlope_of_positiveDominationCoefficient
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    (hsqev : EventuallySquareOne a)
    (hdom : PositiveDominationCoefficient a)
    (hmulti : PositiveMultiscaleHyp a) :
    UniformSlopeHyp a := by
  rcases dirichlet_increment_representation (a := a) ha with ⟨Kdir, hKdir, hrepr⟩
  rcases fejer_representation (a := a) ha with ⟨Kfej, hKfej, hfej⟩
  rcases hdom with ⟨C, hC, hdomC⟩
  rcases hsqev with ⟨Xsq, hsqall⟩
  intro ε hε
  let C' : ℝ := max (C + C * Kfej + Kdir) 1
  have hC'pos : 0 < C' := by
    dsimp [C']
    nlinarith [le_max_right (C + C * Kfej + Kdir) 1]
  let η : ℝ := ε / (2 * C')
  have hη : 0 < η := by
    dsimp [η]
    positivity
  rcases hmulti η hη with ⟨X₁, hX₁⟩
  rcases exists_nat_gt ((4 * C') / ε) with ⟨q, hqgt⟩
  have hqpos_real : (0 : ℝ) < q := by
    have hthreshold_pos : (0 : ℝ) < (4 * C') / ε := by
      positivity
    exact lt_trans hthreshold_pos hqgt
  have hq : 1 ≤ q := by
    exact Nat.succ_le_of_lt (Nat.cast_pos.mp hqpos_real)
  rcases eventually_criticalScale_ge q with ⟨X₂, hX₂⟩
  refine ⟨max Xsq (max X₁ X₂), ?_⟩
  intro X M hX hM hMcrit
  have hXsqle : Xsq ≤ X := by
    exact le_trans (le_max_left _ _) hX
  have hX₁le : X₁ ≤ X := by
    exact le_trans (le_trans (le_max_left X₁ X₂) (le_max_right Xsq (max X₁ X₂))) hX
  have hX₂le : X₂ ≤ X := by
    exact le_trans (le_trans (le_max_right X₁ X₂) (le_max_right Xsq (max X₁ X₂))) hX
  have hsq : SquareOneOnWindow a X := hsqall hXsqle
  have hmass : diagonalMass a X = X := diagonalMass_eq_X_of_squareOne hsq
  have hsum :
      ∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2
        ≤ η * X * criticalScale X := by
    exact hX₁ hX₁le
  have hqleH : q ≤ criticalScale X := by
    exact hX₂ hX₂le
  have hqleH_real : (q : ℝ) ≤ criticalScale X := by
    exact_mod_cast hqleH
  have hHbig : (4 * C') / ε < criticalScale X := by
    nlinarith [hqgt, hqleH_real]
  have hsum_nonneg :
      0 ≤ ∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2 := by
    refine Finset.sum_nonneg ?_
    intro j hj
    exact div_nonneg (E_nonneg a X j) (sq_nonneg (j : ℝ))
  have hsum_small :
      C' * (∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2)
        ≤ (ε / 2) * X * criticalScale X := by
    have hη_eq : C' * (η * X * criticalScale X) ≤ (ε / 2) * X * criticalScale X := by
      have hη_eq_eq : C' * (η * X * criticalScale X) = (ε / 2) * X * criticalScale X := by
        dsimp [η]
        have hcoef : C' * (ε / (2 * C')) = ε / 2 := by
          field_simp [ne_of_gt hC'pos]
        calc
          C' * (ε / (2 * C') * X * criticalScale X)
              = (C' * (ε / (2 * C'))) * ((X : ℝ) * criticalScale X) := by ring
          _ = (ε / 2) * X * criticalScale X := by rw [hcoef]; ring
      exact le_of_eq hη_eq_eq
    exact le_trans (mul_le_mul_of_nonneg_left hsum (le_of_lt hC'pos)) hη_eq
  have herror_small :
      2 * C' * (criticalScale X : ℝ)^2 ≤ (ε / 2) * X * criticalScale X := by
    have hC_small : 2 * C' ≤ (ε / 2) * criticalScale X := by
      have hmul := mul_lt_mul_of_pos_left hHbig (show 0 < ε / 2 by positivity)
      have hleft : (ε / 2) * (4 * C' / ε) = 2 * C' := by
        field_simp [ne_of_gt hε]
        ring
      exact le_of_lt (hleft ▸ hmul)
    have hHsq : (criticalScale X : ℝ)^2 ≤ X := by
      exact_mod_cast criticalScale_sq_le X
    have hH2nonneg : 0 ≤ (criticalScale X : ℝ)^2 := sq_nonneg _
    have hfacnonneg : 0 ≤ (ε / 2) * criticalScale X := by positivity
    calc
      2 * C' * (criticalScale X : ℝ)^2
          ≤ ((ε / 2) * criticalScale X) * (criticalScale X : ℝ)^2 :=
            mul_le_mul_of_nonneg_right hC_small hH2nonneg
      _ ≤ ((ε / 2) * criticalScale X) * X :=
            mul_le_mul_of_nonneg_left hHsq hfacnonneg
      _ = (ε / 2) * X * criticalScale X := by ring
  have hfej_sum_bound :
      ∑ j ∈ Finset.Icc 1 (criticalScale X), fejerMainTerm a X (j - 1) / (j : ℝ)^2
        ≤ (∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2)
          + Kfej * (criticalScale X : ℝ)^2 := by
    have hsum_step :
        ∑ j ∈ Finset.Icc 1 (criticalScale X), fejerMainTerm a X (j - 1) / (j : ℝ)^2
          ≤ ∑ j ∈ Finset.Icc 1 (criticalScale X), (E a X j / (j : ℝ)^2 + Kfej * (j : ℝ)) := by
      refine Finset.sum_le_sum ?_
      intro j hj
      have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
      have hjH : j ≤ criticalScale X := (Finset.mem_Icc.mp hj).2
      have hjleX : j ≤ X := le_trans hjH (criticalScale_le_self X)
      have hmleX : j - 1 ≤ X := by omega
      have hmain := hfej X (j - 1) hmleX hsq
      have hjpos : (0 : ℝ) < j := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hj1
      have hjsqpos : 0 < (j : ℝ)^2 := by positivity
      have hupper : fejerMainTerm a X (j - 1) ≤ E a X j + Kfej * (j : ℝ)^3 := by
        have hrew : E a X ((j - 1) + 1) = E a X j := by
          congr
          exact Nat.sub_add_cancel hj1
        rw [hrew] at hmain
        have hpow : (((j - 1 : ℕ) : ℝ) + 1) = (j : ℝ) := by
          exact_mod_cast (Nat.sub_add_cancel hj1)
        rw [hpow] at hmain
        have hlow := (abs_le.mp hmain).1
        nlinarith
      have hdiv : fejerMainTerm a X (j - 1) / (j : ℝ)^2
          ≤ E a X j / (j : ℝ)^2 + Kfej * (j : ℝ) := by
        have htmp : fejerMainTerm a X (j - 1) / (j : ℝ)^2
            ≤ (E a X j + Kfej * (j : ℝ)^3) / (j : ℝ)^2 := by
          exact div_le_div_of_nonneg_right hupper (le_of_lt hjsqpos)
        have hjne : (j : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hj1))
        calc
          fejerMainTerm a X (j - 1) / (j : ℝ)^2
              ≤ (E a X j + Kfej * (j : ℝ)^3) / (j : ℝ)^2 := htmp
          _ = E a X j / (j : ℝ)^2 + Kfej * (j : ℝ) := by
              field_simp [hjne]
      exact hdiv
    have hsum_rearrange :
        ∑ j ∈ Finset.Icc 1 (criticalScale X), (E a X j / (j : ℝ)^2 + Kfej * (j : ℝ))
          = (∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2)
            + Kfej * (∑ j ∈ Finset.Icc 1 (criticalScale X), (j : ℝ)) := by
      rw [Finset.sum_add_distrib]
      rw [← mul_sum (s := Finset.Icc 1 (criticalScale X)) (c := Kfej) (f := fun j => (j : ℝ))]
    have hlin : ∑ j ∈ Finset.Icc 1 (criticalScale X), (j : ℝ) ≤ (criticalScale X : ℝ)^2 :=
      sum_Icc_cast_id_le_sq (criticalScale X)
    calc
      ∑ j ∈ Finset.Icc 1 (criticalScale X), fejerMainTerm a X (j - 1) / (j : ℝ)^2
          ≤ ∑ j ∈ Finset.Icc 1 (criticalScale X), (E a X j / (j : ℝ)^2 + Kfej * (j : ℝ)) := hsum_step
      _ = (∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2)
            + Kfej * (∑ j ∈ Finset.Icc 1 (criticalScale X), (j : ℝ)) := hsum_rearrange
      _ ≤ (∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2)
            + Kfej * (criticalScale X : ℝ)^2 := by
          exact add_le_add_right (mul_le_mul_of_nonneg_left hlin hKfej) _
  have hctrl_main :
      |dirichletMainTerm a X M - diagonalMass a X|
        ≤ C' * (∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2)
          + C' * (criticalScale X : ℝ)^2 := by
    have hmain := hdomC X M hM hMcrit
    have hC_le : C ≤ C' := by
      dsimp [C']
      have h1 : C ≤ C + C * Kfej + Kdir := by nlinarith [hC, hKfej, hKdir]
      exact le_trans h1 (le_max_left _ _)
    have hCK_le : C * Kfej ≤ C' := by
      dsimp [C']
      have h1 : C * Kfej ≤ C + C * Kfej + Kdir := by nlinarith [hC, hKfej, hKdir]
      exact le_trans h1 (le_max_left _ _)
    calc
      |dirichletMainTerm a X M - diagonalMass a X|
          ≤ C * (∑ j ∈ Finset.Icc 1 (criticalScale X), fejerMainTerm a X (j - 1) / (j : ℝ)^2) := hmain
      _ ≤ C * ((∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2)
            + Kfej * (criticalScale X : ℝ)^2) := by
            exact mul_le_mul_of_nonneg_left hfej_sum_bound hC
      _ = C * (∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2)
            + (C * Kfej) * (criticalScale X : ℝ)^2 := by ring
      _ ≤ C' * (∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2)
            + C' * (criticalScale X : ℝ)^2 := by
            exact add_le_add
              (mul_le_mul_of_nonneg_right hC_le hsum_nonneg)
              (mul_le_mul_of_nonneg_right hCK_le (sq_nonneg (criticalScale X : ℝ)))
  have hrepr_main :
      |(E a X (M + 1) - E a X M) - dirichletMainTerm a X M|
        ≤ C' * (criticalScale X : ℝ)^2 := by
    have hMX : M ≤ X := by
      exact le_trans hMcrit (criticalScale_le_self X)
    have hmain := hrepr X M hMX hsq
    have hK_le : Kdir ≤ C' := by
      dsimp [C']
      have h1 : Kdir ≤ C + C * Kfej + Kdir := by nlinarith [hC, hKfej, hKdir]
      exact le_trans h1 (le_max_left _ _)
    have hMcrit_real : (M : ℝ) ≤ criticalScale X := by
      exact_mod_cast hMcrit
    calc
      |(E a X (M + 1) - E a X M) - dirichletMainTerm a X M|
          ≤ Kdir * (M : ℝ)^2 := hmain
      _ ≤ Kdir * (criticalScale X : ℝ)^2 := by
          have hsquare : (M : ℝ)^2 ≤ (criticalScale X : ℝ)^2 := by
            have hmul := mul_le_mul hMcrit_real hMcrit_real (by positivity : 0 ≤ (M : ℝ)) (by positivity : 0 ≤ (criticalScale X : ℝ))
            simpa [pow_two] using hmul
          exact mul_le_mul_of_nonneg_left hsquare hKdir
      _ ≤ C' * (criticalScale X : ℝ)^2 := by
          exact mul_le_mul_of_nonneg_right hK_le (sq_nonneg (criticalScale X : ℝ))
  calc
    |(E a X (M + 1) - E a X M) - X|
        = |((E a X (M + 1) - E a X M) - dirichletMainTerm a X M)
            + (dirichletMainTerm a X M - diagonalMass a X)| := by
              rw [hmass]
              congr 1
              ring
    _ ≤ |(E a X (M + 1) - E a X M) - dirichletMainTerm a X M|
          + |dirichletMainTerm a X M - diagonalMass a X| := by
            exact abs_add _ _
    _ ≤ C' * (criticalScale X : ℝ)^2
          + (C' * (∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2)
              + C' * (criticalScale X : ℝ)^2) := by
            exact add_le_add hrepr_main hctrl_main
    _ = C' * (∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2)
          + 2 * C' * (criticalScale X : ℝ)^2 := by ring
    _ ≤ (ε / 2) * X * criticalScale X + (ε / 2) * X * criticalScale X := by
          exact add_le_add hsum_small herror_small
    _ ≤ ε * X * criticalScale X := by
          ring_nf
          exact le_rfl

/--
A more paper-shaped Section 4 criterion: once coefficient-level positive domination is available,
the positive multiscale estimate alone is enough to recover global prefix cancellation.
-/
theorem positive_multiscale_criterion_positiveDomination
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    (hsqev : EventuallySquareOne a)
    (hdom : PositiveDominationCoefficient a)
    (hmulti : PositiveMultiscaleHyp a) :
    PrefixLittleO a := by
  apply uniform_slope_criterion (a := a) ha hsqev
  exact uniformSlope_of_positiveDominationCoefficient ha hsqev hdom hmulti

end PositiveDominationCoefficient

end FixedShiftLiouville

namespace FixedShiftLiouville

section HarmonicWeightIdentity

/-- The positive multiscale energy from Section 5. -/
def harmonicEnergy (a : ℕ → ℝ) (X H : ℕ) : ℝ :=
  ∑ M ∈ Finset.Icc 1 H, E a X M / (M : ℝ)^2

/-- The harmonic shell weight appearing after interchanging the Section 5 triangular sum. -/
def harmonicWeight (H t : ℕ) : ℝ :=
  ∑ M ∈ Finset.Icc (t + 1) H, ((M - t : ℕ) : ℝ) / (M : ℝ)^2

/-- The Section 5 weighted-pair accumulator before shellwise reorganization. -/
def harmonicPairAccumulator (a : ℕ → ℝ) (X H : ℕ) : ℝ :=
  ∑ M ∈ Finset.Icc 1 H, weightedPairs a X (M - 1) / (M : ℝ)^2

/-- Reindexing the Cesàro quartic sum over `Icc 1 M`. -/
lemma C_eq_sum_Icc (a : ℕ → ℝ) (X M : ℕ) :
    C a X M = ∑ t ∈ Finset.Icc 1 M, P a X t := by
  unfold C
  rw [Finset.sum_Icc_eq_sum_range]
  refine Finset.sum_congr rfl ?_
  intro i hi
  simp [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-- Reindexing the weighted quartic profile over `Icc 1 M`. -/
lemma weightedPairs_eq_sum_Icc (a : ℕ → ℝ) (X M : ℕ) :
    weightedPairs a X M
      = ∑ t ∈ Finset.Icc 1 M, ((M + 1 - t : ℕ) : ℝ) * P a X t := by
  unfold weightedPairs
  rw [Finset.sum_Icc_eq_sum_range]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hcoef : M - i = M + 1 - (i + 1) := by omega
  rw [hcoef]
  rw [Nat.add_comm i 1]

/-- The harmonic weights are termwise nonnegative. -/
lemma harmonicWeight_nonneg (H t : ℕ) : 0 ≤ harmonicWeight H t := by
  unfold harmonicWeight
  refine Finset.sum_nonneg ?_
  intro M hM
  positivity

/-- A crude Section 5 upper bound: the harmonic weight is controlled by the harmonic tail. -/
lemma harmonicWeight_le_harmonicTail (H t : ℕ) :
    harmonicWeight H t ≤ ∑ M ∈ Finset.Icc (t + 1) H, (1 : ℝ) / (M : ℝ) := by
  unfold harmonicWeight
  refine Finset.sum_le_sum ?_
  intro M hM
  have hMt : M - t ≤ M := by omega
  have hcoeff : (((M - t : ℕ) : ℝ)) ≤ M := by
    exact_mod_cast hMt
  have hsq : 0 ≤ (M : ℝ)^2 := sq_nonneg (M : ℝ)
  have htmp : (((M - t : ℕ) : ℝ)) / (M : ℝ)^2 ≤ (M : ℝ) / (M : ℝ)^2 := by
    exact div_le_div_of_nonneg_right hcoeff hsq
  have hM1 : 1 ≤ M := by
    exact le_trans (Nat.succ_pos t) (Finset.mem_Icc.mp hM).1
  have hM0 : (M : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hM1))
  calc
    (((M - t : ℕ) : ℝ)) / (M : ℝ)^2 ≤ (M : ℝ) / (M : ℝ)^2 := htmp
    _ = (1 : ℝ) / (M : ℝ) := by
        field_simp [hM0]

/-- Expanding the Fejér main term inside the Section 5 harmonic sum. -/
lemma harmonicMainCoefficient_expand (a : ℕ → ℝ) (X H : ℕ) :
    ∑ M ∈ Finset.Icc 1 H, fejerMainTerm a X (M - 1) / (M : ℝ)^2
      = diagonalMass a X * (∑ M ∈ Finset.Icc 1 H, (1 : ℝ) / (M : ℝ))
        + 2 * harmonicPairAccumulator a X H := by
  unfold harmonicPairAccumulator
  calc
    ∑ M ∈ Finset.Icc 1 H, fejerMainTerm a X (M - 1) / (M : ℝ)^2
        = ∑ M ∈ Finset.Icc 1 H,
            (diagonalMass a X * ((1 : ℝ) / (M : ℝ))
              + 2 * (weightedPairs a X (M - 1) / (M : ℝ)^2)) := by
            refine Finset.sum_congr rfl ?_
            intro M hM
            have hM1 : 1 ≤ M := (Finset.mem_Icc.mp hM).1
            have hM0 : (M : ℝ) ≠ 0 := by
              exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hM1))
            calc
              fejerMainTerm a X (M - 1) / (M : ℝ)^2
                  = (((M : ℝ) * diagonalMass a X)
                      + 2 * weightedPairs a X (M - 1)) / (M : ℝ)^2 := by
                        have hMpred : M - 1 + 1 = M := Nat.sub_add_cancel hM1
                        have hMpredR : (((M - 1 : ℕ) : ℝ) + 1) = (M : ℝ) := by
                          exact_mod_cast hMpred
                        simp [fejerMainTerm, hMpredR]
              _ = diagonalMass a X * ((1 : ℝ) / (M : ℝ))
                    + 2 * (weightedPairs a X (M - 1) / (M : ℝ)^2) := by
                      field_simp [hM0]
    _ = (∑ M ∈ Finset.Icc 1 H, diagonalMass a X * ((1 : ℝ) / (M : ℝ)))
          + ∑ M ∈ Finset.Icc 1 H,
              2 * (weightedPairs a X (M - 1) / (M : ℝ)^2) := by
            rw [Finset.sum_add_distrib]
    _ = diagonalMass a X * (∑ M ∈ Finset.Icc 1 H, (1 : ℝ) / (M : ℝ))
          + 2 * harmonicPairAccumulator a X H := by
            unfold harmonicPairAccumulator
            rw [← mul_sum (s := Finset.Icc 1 H) (c := diagonalMass a X) (f := fun M => (1 : ℝ) / (M : ℝ))]
            rw [← mul_sum (s := Finset.Icc 1 H) (c := (2 : ℝ)) (f := fun M => weightedPairs a X (M - 1) / (M : ℝ)^2)]

/-- A pointwise error estimate for the Section 5 harmonic-energy summand. -/
lemma harmonicEnergy_term_error
    {a : ℕ → ℝ} (ha : BoundedByOne a)
    {X H M : ℕ} (hHX : H ≤ X)
    (hM : M ∈ Finset.Icc 1 H) (hsq : SquareOneOnWindow a X) :
    ∃ K : ℝ, 0 ≤ K ∧
      |E a X M / (M : ℝ)^2 - fejerMainTerm a X (M - 1) / (M : ℝ)^2| ≤ K * M := by
  rcases fejer_representation (a := a) ha with ⟨K, hK, hfej⟩
  refine ⟨K, hK, ?_⟩
  have hM1 : 1 ≤ M := (Finset.mem_Icc.mp hM).1
  have hMleH : M ≤ H := (Finset.mem_Icc.mp hM).2
  have hpredleX : M - 1 ≤ X := by
    exact le_trans (le_trans (Nat.sub_le M 1) hMleH) hHX
  have hmain := hfej X (M - 1) hpredleX hsq
  have hM0 : (M : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hM1))
  have hM2 : 0 ≤ (M : ℝ)^2 := sq_nonneg (M : ℝ)
  have hdiv :
      |(E a X M - fejerMainTerm a X (M - 1)) / (M : ℝ)^2|
        ≤ (K * (M : ℝ)^3) / (M : ℝ)^2 := by
    have hrew : E a X ((M - 1) + 1) = E a X M := by
      congr
      exact Nat.sub_add_cancel hM1
    rw [hrew] at hmain
    have hpow : (((M - 1 : ℕ) : ℝ) + 1) = (M : ℝ) := by
      exact_mod_cast (Nat.sub_add_cancel hM1)
    rw [hpow] at hmain
    rw [abs_div, abs_of_nonneg hM2]
    exact div_le_div_of_nonneg_right hmain hM2
  have habs_div :
      |E a X M / (M : ℝ)^2 - fejerMainTerm a X (M - 1) / (M : ℝ)^2|
        = |(E a X M - fejerMainTerm a X (M - 1)) / (M : ℝ)^2| := by
    congr 1
    field_simp [hM0]
  rw [habs_div]
  calc
    |(E a X M - fejerMainTerm a X (M - 1)) / (M : ℝ)^2|
        ≤ (K * (M : ℝ)^3) / (M : ℝ)^2 := hdiv
    _ = K * M := by
        field_simp [hM0]

/--
A first exact Section 5 harmonic identity: the positive multiscale sum equals the diagonal term
plus the weighted-pair accumulator, up to an `O(H²)` error coming from Section 3.

This is the clean pre-shell form of Proposition 5.2, before the triangular `M`/`t` sum has been
reorganized into the explicit harmonic weight `ν_H(t)`.
-/
theorem harmonic_weight_identity_preShell
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    {X H : ℕ} (hHX : H ≤ X)
    (hsq : SquareOneOnWindow a X) :
    ∃ K : ℝ, 0 ≤ K ∧
      |harmonicEnergy a X H
        - diagonalMass a X * (∑ M ∈ Finset.Icc 1 H, (1 : ℝ) / (M : ℝ))
        - 2 * harmonicPairAccumulator a X H| ≤ K * H^2 := by
  rcases fejer_representation (a := a) ha with ⟨K, hK, hfej⟩
  refine ⟨K, hK, ?_⟩
  have hexpand :
      harmonicEnergy a X H
        - diagonalMass a X * (∑ M ∈ Finset.Icc 1 H, (1 : ℝ) / (M : ℝ))
        - 2 * harmonicPairAccumulator a X H
        = ∑ M ∈ Finset.Icc 1 H,
            (E a X M / (M : ℝ)^2 - fejerMainTerm a X (M - 1) / (M : ℝ)^2) := by
    unfold harmonicEnergy
    have hmainCoeff := harmonicMainCoefficient_expand a X H
    calc
      (∑ M ∈ Finset.Icc 1 H, E a X M / (M : ℝ)^2)
        - diagonalMass a X * (∑ M ∈ Finset.Icc 1 H, (1 : ℝ) / (M : ℝ))
        - 2 * harmonicPairAccumulator a X H
          = (∑ M ∈ Finset.Icc 1 H, E a X M / (M : ℝ)^2)
            - (diagonalMass a X * (∑ M ∈ Finset.Icc 1 H, (1 : ℝ) / (M : ℝ))
                + 2 * harmonicPairAccumulator a X H) := by ring
      _ = (∑ M ∈ Finset.Icc 1 H, E a X M / (M : ℝ)^2)
            - (∑ M ∈ Finset.Icc 1 H, fejerMainTerm a X (M - 1) / (M : ℝ)^2) := by
              rw [hmainCoeff]
      _ = ∑ M ∈ Finset.Icc 1 H,
            (E a X M / (M : ℝ)^2 - fejerMainTerm a X (M - 1) / (M : ℝ)^2) := by
              rw [← Finset.sum_sub_distrib]
  rw [hexpand]
  calc
    |∑ M ∈ Finset.Icc 1 H,
        (E a X M / (M : ℝ)^2 - fejerMainTerm a X (M - 1) / (M : ℝ)^2)|
        ≤ ∑ M ∈ Finset.Icc 1 H,
            |E a X M / (M : ℝ)^2 - fejerMainTerm a X (M - 1) / (M : ℝ)^2| := by
              exact abs_sum_le_sum_abs (fun M => E a X M / (M : ℝ)^2 - fejerMainTerm a X (M - 1) / (M : ℝ)^2)
    _ ≤ ∑ M ∈ Finset.Icc 1 H, K * M := by
          refine Finset.sum_le_sum ?_
          intro M hM
          have hM1 : 1 ≤ M := (Finset.mem_Icc.mp hM).1
          have hMleH : M ≤ H := (Finset.mem_Icc.mp hM).2
          have hpredleX : M - 1 ≤ X := by
            exact le_trans (le_trans (Nat.sub_le M 1) hMleH) hHX
          have hmain := hfej X (M - 1) hpredleX hsq
          have hM0 : (M : ℝ) ≠ 0 := by
            exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hM1))
          have hM2 : 0 ≤ (M : ℝ)^2 := sq_nonneg (M : ℝ)
          have hdiv :
              |(E a X M - fejerMainTerm a X (M - 1)) / (M : ℝ)^2|
                ≤ (K * (M : ℝ)^3) / (M : ℝ)^2 := by
            have hrew : E a X ((M - 1) + 1) = E a X M := by
              congr
              exact Nat.sub_add_cancel hM1
            rw [hrew] at hmain
            have hpow : (((M - 1 : ℕ) : ℝ) + 1) = (M : ℝ) := by
              exact_mod_cast (Nat.sub_add_cancel hM1)
            rw [hpow] at hmain
            rw [abs_div, abs_of_nonneg hM2]
            exact div_le_div_of_nonneg_right hmain hM2
          have habs_div :
              |E a X M / (M : ℝ)^2 - fejerMainTerm a X (M - 1) / (M : ℝ)^2|
                = |(E a X M - fejerMainTerm a X (M - 1)) / (M : ℝ)^2| := by
            congr 1
            field_simp [hM0]
          rw [habs_div]
          calc
            |(E a X M - fejerMainTerm a X (M - 1)) / (M : ℝ)^2|
                ≤ (K * (M : ℝ)^3) / (M : ℝ)^2 := hdiv
            _ = K * M := by
                field_simp [hM0]
    _ = K * (∑ M ∈ Finset.Icc 1 H, (M : ℝ)) := by
          rw [← mul_sum (s := Finset.Icc 1 H) (c := K) (f := fun M => (M : ℝ))]
    _ ≤ K * H^2 := by
          exact mul_le_mul_of_nonneg_left (sum_Icc_cast_id_le_sq H) hK

end HarmonicWeightIdentity

end FixedShiftLiouville

namespace FixedShiftLiouville

section DyadicShells

/-- Dyadic shell partial sums of the quartic profile. -/
def Qshell (a : ℕ → ℝ) (X k u : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc (2 ^ k) u, P a X t

/-- The top of the `k`-th dyadic shell inside `[1,H-1]`. -/
def shellTop (H k : ℕ) : ℕ :=
  min (2 ^ (k + 1) - 1) (H - 1)

@[simp] lemma Qshell_eq_sum (a : ℕ → ℝ) (X k u : ℕ) :
    Qshell a X k u = ∑ t ∈ Finset.Icc (2 ^ k) u, P a X t := by
  rfl

@[simp] lemma Qshell_zero_of_lt
    (a : ℕ → ℝ) (X k u : ℕ) (hu : u < 2 ^ k) :
    Qshell a X k u = 0 := by
  unfold Qshell
  simp [Finset.Icc_eq_empty_of_lt hu]

lemma Qshell_succ
    (a : ℕ → ℝ) (X k u : ℕ) (hu : 2 ^ k ≤ u) :
    Qshell a X k (u + 1) = Qshell a X k u + P a X (u + 1) := by
  unfold Qshell
  rw [show Finset.Icc (2 ^ k) (u + 1) = insert (u + 1) (Finset.Icc (2 ^ k) u) by
    ext t
    simp [Finset.mem_Icc]
    omega]
  simp [hu, Nat.lt_succ_self]
  ring_nf

/-- Abel summation on initial segments. -/
lemma abel_range (w p : ℕ → ℝ) :
    ∀ m : ℕ,
      ∑ i ∈ Finset.range (m + 1), w i * p i
        = w m * ∑ i ∈ Finset.range (m + 1), p i
          + ∑ i ∈ Finset.range m,
              (w i - w (i + 1)) * ∑ j ∈ Finset.range (i + 1), p j := by
  intro m
  induction m with
  | zero =>
      simp
  | succ m hm =>
      simp [Finset.sum_range_succ, hm, add_assoc, add_comm, add_left_comm, sub_eq_add_neg, left_distrib, right_distrib]
      ring_nf

/-- Abel summation on a finite interval. -/
lemma abel_Icc
    (w p : ℕ → ℝ) {L U : ℕ} (hLU : L ≤ U) (hUpos : 1 ≤ U) :
    ∑ t ∈ Finset.Icc L U, w t * p t
      = w U * ∑ t ∈ Finset.Icc L U, p t
        + ∑ u ∈ Finset.Icc L (U - 1),
            (w u - w (u + 1)) * ∑ t ∈ Finset.Icc L u, p t := by
  let m : ℕ := U - L
  have hm : U = L + m := by
    dsimp [m]
    omega
  have hsumU :
      ∑ t ∈ Finset.Icc L U, p t = ∑ i ∈ Finset.range (m + 1), p (L + i) := by
    rw [hm, Finset.sum_Icc_eq_sum_range]
    have hlen : L + m + 1 - L = m + 1 := by omega
    rw [hlen]
  have hsumLm :
      ∑ t ∈ Finset.Icc L (L + m), p t = ∑ i ∈ Finset.range (m + 1), p (L + i) := by
    rw [Finset.sum_Icc_eq_sum_range]
    have hlen : L + m + 1 - L = m + 1 := by omega
    rw [hlen]
  have hmain := abel_range (fun i => w (L + i)) (fun i => p (L + i)) m
  calc
    ∑ t ∈ Finset.Icc L U, w t * p t
        = ∑ i ∈ Finset.range (m + 1), w (L + i) * p (L + i) := by
            rw [hm, Finset.sum_Icc_eq_sum_range]
            have hlen : L + m + 1 - L = m + 1 := by omega
            rw [hlen]
    _ = w (L + m) * ∑ i ∈ Finset.range (m + 1), p (L + i)
          + ∑ i ∈ Finset.range m,
              (w (L + i) - w (L + i + 1)) * ∑ j ∈ Finset.range (i + 1), p (L + j) := by
            simpa using hmain
    _ = w U * ∑ t ∈ Finset.Icc L U, p t
          + ∑ i ∈ Finset.range m,
              (w (L + i) - w (L + i + 1)) * ∑ j ∈ Finset.range (i + 1), p (L + j) := by
            rw [hm, hsumLm]
    _ = w U * ∑ t ∈ Finset.Icc L U, p t
          + ∑ u ∈ Finset.Icc L (U - 1),
              (w u - w (u + 1)) * ∑ t ∈ Finset.Icc L u, p t := by
            congr 1
            rw [Finset.sum_Icc_eq_sum_range]
            have hUminus : U - 1 + 1 = U := by omega
            have hlen : U - 1 + 1 - L = m := by
              dsimp [m]
              rw [hUminus]
            rw [hlen]
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hprefix :
                ∑ t ∈ Finset.Icc L (L + i), p t = ∑ j ∈ Finset.range (i + 1), p (L + j) := by
              rw [Finset.sum_Icc_eq_sum_range]
              have hlen2 : L + i + 1 - L = i + 1 := by omega
              rw [hlen2]
            rw [hprefix]

/-- Exact finite-difference identity for the harmonic weights from Section 5. -/
lemma harmonicWeight_difference
    {H u : ℕ} (hu : u + 1 ≤ H) :
    harmonicWeight H u - harmonicWeight H (u + 1)
      = ∑ M ∈ Finset.Icc (u + 1) H, (1 : ℝ) / (M : ℝ)^2 := by
  have hsplit : Finset.Icc (u + 1) H = insert (u + 1) (Finset.Icc (u + 2) H) := by
    ext M
    simp [Finset.mem_Icc]
    omega
  have hnotmem : u + 1 ∉ Finset.Icc (u + 2) H := by
    simp [Finset.mem_Icc]
  have hsub :
      ∑ M ∈ Finset.Icc (u + 2) H, (((M - u : ℕ) : ℝ) / (M : ℝ)^2)
        - ∑ M ∈ Finset.Icc (u + 2) H, (((M - (u + 1) : ℕ) : ℝ) / (M : ℝ)^2)
        = ∑ M ∈ Finset.Icc (u + 2) H, (1 : ℝ) / (M : ℝ)^2 := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro M hM
    have hnat : M - u = (M - (u + 1)) + 1 := by
      have hMu : u + 2 ≤ M := (Finset.mem_Icc.mp hM).1
      omega
    have hcast : ((M - u : ℕ) : ℝ) - ((M - (u + 1) : ℕ) : ℝ) = 1 := by
      rw [hnat, Nat.cast_add, Nat.cast_one]
      ring
    calc
      ((M - u : ℕ) : ℝ) / (M : ℝ)^2
          - ((M - (u + 1) : ℕ) : ℝ) / (M : ℝ)^2
          = (((M - u : ℕ) : ℝ) - ((M - (u + 1) : ℕ) : ℝ)) / (M : ℝ)^2 := by ring
      _ = (1 : ℝ) / (M : ℝ)^2 := by rw [hcast]
  unfold harmonicWeight
  have hexpand :
      ∑ M ∈ Finset.Icc (u + 1) H, (((M - u : ℕ) : ℝ) / (M : ℝ)^2)
        = (((u + 1 - u : ℕ) : ℝ) / (((u + 1 : ℕ) : ℝ)^2))
            + ∑ M ∈ Finset.Icc (u + 2) H, (((M - u : ℕ) : ℝ) / (M : ℝ)^2) := by
    calc
      ∑ M ∈ Finset.Icc (u + 1) H, (((M - u : ℕ) : ℝ) / (M : ℝ)^2)
          = ∑ M ∈ insert (u + 1) (Finset.Icc (u + 2) H), (((M - u : ℕ) : ℝ) / (M : ℝ)^2) := by
              simpa only [hsplit]
      _ = (((u + 1 - u : ℕ) : ℝ) / (((u + 1 : ℕ) : ℝ)^2))
            + ∑ M ∈ Finset.Icc (u + 2) H, (((M - u : ℕ) : ℝ) / (M : ℝ)^2) := by
              rw [Finset.sum_insert hnotmem]
  have hlead :
      (((u + 1 - u : ℕ) : ℝ) / (((u + 1 : ℕ) : ℝ)^2))
        = (1 : ℝ) / (((u + 1 : ℕ) : ℝ)^2) := by
    norm_num
  have htarget :
      ∑ M ∈ Finset.Icc (u + 1) H, (1 : ℝ) / (M : ℝ)^2
        = (1 : ℝ) / (((u + 1 : ℕ) : ℝ)^2)
            + ∑ M ∈ Finset.Icc (u + 2) H, (1 : ℝ) / (M : ℝ)^2 := by
    calc
      ∑ M ∈ Finset.Icc (u + 1) H, (1 : ℝ) / (M : ℝ)^2
          = ∑ M ∈ insert (u + 1) (Finset.Icc (u + 2) H), (1 : ℝ) / (M : ℝ)^2 := by
              simpa only [hsplit]
      _ = (1 : ℝ) / (((u + 1 : ℕ) : ℝ)^2)
            + ∑ M ∈ Finset.Icc (u + 2) H, (1 : ℝ) / (M : ℝ)^2 := by
              rw [Finset.sum_insert hnotmem]
  rw [hexpand, hlead]
  calc
    (1 : ℝ) / (((u + 1 : ℕ) : ℝ)^2)
        + ∑ M ∈ Finset.Icc (u + 2) H, (((M - u : ℕ) : ℝ) / (M : ℝ)^2)
        - ∑ M ∈ Finset.Icc (u + 2) H, (((M - (u + 1) : ℕ) : ℝ) / (M : ℝ)^2)
        = (1 : ℝ) / (((u + 1 : ℕ) : ℝ)^2)
            + (∑ M ∈ Finset.Icc (u + 2) H, (((M - u : ℕ) : ℝ) / (M : ℝ)^2)
              - ∑ M ∈ Finset.Icc (u + 2) H, (((M - (u + 1) : ℕ) : ℝ) / (M : ℝ)^2)) := by ring
    _ = (1 : ℝ) / (((u + 1 : ℕ) : ℝ)^2)
            + ∑ M ∈ Finset.Icc (u + 2) H, (1 : ℝ) / (M : ℝ)^2 := by
          rw [hsub]
    _ = ∑ M ∈ Finset.Icc (u + 1) H, (1 : ℝ) / (M : ℝ)^2 := by
          rw [htarget]


/-- Abel summation on one dyadic shell. -/
theorem shell_summation_by_parts
    (a : ℕ → ℝ) (X H k : ℕ) :
    ∑ t ∈ Finset.Icc (2 ^ k) (shellTop H k),
      harmonicWeight H t * P a X t
      = harmonicWeight H (shellTop H k) * Qshell a X k (shellTop H k)
        + ∑ u ∈ Finset.Icc (2 ^ k) (shellTop H k - 1),
            (harmonicWeight H u - harmonicWeight H (u + 1)) * Qshell a X k u := by
  by_cases hshell : 2 ^ k ≤ shellTop H k
  · simpa [Qshell, shellTop] using
      (abel_Icc (w := harmonicWeight H) (p := P a X) hshell (le_trans (Nat.one_le_two_pow) hshell))
  · have hlt : shellTop H k < 2 ^ k := by omega
    have hlt2 : shellTop H k - 1 < 2 ^ k := by omega
    simp [Qshell, Finset.Icc_eq_empty_of_lt hlt, Finset.Icc_eq_empty_of_lt hlt2]

end DyadicShells

end FixedShiftLiouville


namespace FixedShiftLiouville

section HarmonicWeightExact

@[simp] lemma harmonicWeight_eq_zero_of_ge
    {H t : ℕ} (ht : H ≤ t) :
    harmonicWeight H t = 0 := by
  unfold harmonicWeight
  have hlt : H < t + 1 := Nat.lt_succ_of_le ht
  rw [Finset.Icc_eq_empty_of_lt hlt]
  simp

@[simp] lemma harmonicWeight_self_zero (H : ℕ) :
    harmonicWeight H H = 0 := by
  exact harmonicWeight_eq_zero_of_ge (H := H) (t := H) (le_rfl)

lemma harmonicWeight_succ_right
    (H t : ℕ) (ht : t ≤ H) :
    harmonicWeight (H + 1) t
      = harmonicWeight H t + (((H + 1 - t : ℕ) : ℝ) / (((H + 1 : ℕ) : ℝ)^2)) := by
  unfold harmonicWeight
  have hsplit : Finset.Icc (t + 1) (H + 1) = insert (H + 1) (Finset.Icc (t + 1) H) := by
    ext m
    simp [Finset.mem_Icc]
    omega
  have hnotmem : H + 1 ∉ Finset.Icc (t + 1) H := by
    simp [Finset.mem_Icc]
  rw [hsplit]
  rw [Finset.sum_insert hnotmem]
  ring

/-- Exact triangular reorganization of the Section 5 pre-shell accumulator. -/
theorem harmonicPairAccumulator_eq_weightedSum
    (a : ℕ → ℝ) (X H : ℕ) :
    harmonicPairAccumulator a X H
      = ∑ t ∈ Finset.Icc 1 (H - 1), harmonicWeight H t * P a X t := by
  induction H with
  | zero =>
      simp [harmonicPairAccumulator, harmonicWeight]
  | succ H hIH =>
      have hacc :
          harmonicPairAccumulator a X (H + 1)
            = harmonicPairAccumulator a X H
              + weightedPairs a X H / (((H + 1 : ℕ) : ℝ)^2) := by
        unfold harmonicPairAccumulator
        rw [Finset.sum_Icc_succ_top (show 1 ≤ H + 1 by omega)]
        have hidx : H + 1 - 1 = H := by omega
        rw [hidx]
      have hnew :
          weightedPairs a X H / (((H + 1 : ℕ) : ℝ)^2)
            = ∑ t ∈ Finset.Icc 1 H,
                ((((H + 1 - t : ℕ) : ℝ) / (((H + 1 : ℕ) : ℝ)^2)) * P a X t) := by
        rw [weightedPairs_eq_sum_Icc]
        let d : ℝ := (((H + 1 : ℕ) : ℝ)^2)
        calc
          (∑ t ∈ Finset.Icc 1 H, ((H + 1 - t : ℕ) : ℝ) * P a X t) / d
              = (1 / d) * ∑ t ∈ Finset.Icc 1 H, ((H + 1 - t : ℕ) : ℝ) * P a X t := by ring
          _ = ∑ t ∈ Finset.Icc 1 H, (1 / d) * (((H + 1 - t : ℕ) : ℝ) * P a X t) := by
                rw [mul_sum]
          _ = ∑ t ∈ Finset.Icc 1 H, ((((H + 1 - t : ℕ) : ℝ) / d) * P a X t) := by
                refine Finset.sum_congr rfl ?_
                intro t ht
                ring

      have hold_extend :
          ∑ t ∈ Finset.Icc 1 H, harmonicWeight H t * P a X t
            = ∑ t ∈ Finset.Icc 1 (H - 1), harmonicWeight H t * P a X t := by
        by_cases hH : H = 0
        · subst hH
          simp
        · have h1 : 1 ≤ H := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hH)
          have hsplit : Finset.Icc 1 H = insert H (Finset.Icc 1 (H - 1)) := by
            ext t
            simp [Finset.mem_Icc]
            omega
          have hnotmem : H ∉ Finset.Icc 1 (H - 1) := by
            simp [Finset.mem_Icc]
            omega
          rw [hsplit]
          rw [Finset.sum_insert hnotmem]
          simp [harmonicWeight_self_zero]
      have hshell :
          ∑ t ∈ Finset.Icc 1 H, harmonicWeight (H + 1) t * P a X t
            = ∑ t ∈ Finset.Icc 1 H, harmonicWeight H t * P a X t
              + ∑ t ∈ Finset.Icc 1 H,
                  ((((H + 1 - t : ℕ) : ℝ) / (((H + 1 : ℕ) : ℝ)^2)) * P a X t) := by
        calc
          ∑ t ∈ Finset.Icc 1 H, harmonicWeight (H + 1) t * P a X t
              = ∑ t ∈ Finset.Icc 1 H,
                  ((harmonicWeight H t
                    + (((H + 1 - t : ℕ) : ℝ) / (((H + 1 : ℕ) : ℝ)^2))) * P a X t) := by
                    refine Finset.sum_congr rfl ?_
                    intro t ht
                    have htH : t ≤ H := (Finset.mem_Icc.mp ht).2
                    rw [harmonicWeight_succ_right H t htH]
          _ = ∑ t ∈ Finset.Icc 1 H,
                  (harmonicWeight H t * P a X t
                    + ((((H + 1 - t : ℕ) : ℝ) / (((H + 1 : ℕ) : ℝ)^2)) * P a X t)) := by
                    refine Finset.sum_congr rfl ?_
                    intro t ht
                    ring
          _ = ∑ t ∈ Finset.Icc 1 H, harmonicWeight H t * P a X t
                + ∑ t ∈ Finset.Icc 1 H,
                    ((((H + 1 - t : ℕ) : ℝ) / (((H + 1 : ℕ) : ℝ)^2)) * P a X t) := by
                    rw [Finset.sum_add_distrib]
      calc
        harmonicPairAccumulator a X (H + 1)
            = harmonicPairAccumulator a X H
                + weightedPairs a X H / (((H + 1 : ℕ) : ℝ)^2) := hacc
        _ = (∑ t ∈ Finset.Icc 1 (H - 1), harmonicWeight H t * P a X t)
              + weightedPairs a X H / (((H + 1 : ℕ) : ℝ)^2) := by rw [hIH]
        _ = (∑ t ∈ Finset.Icc 1 H, harmonicWeight H t * P a X t)
              + weightedPairs a X H / (((H + 1 : ℕ) : ℝ)^2) := by
              rw [hold_extend]
        _ = (∑ t ∈ Finset.Icc 1 H, harmonicWeight H t * P a X t)
              + ∑ t ∈ Finset.Icc 1 H,
                  ((((H + 1 - t : ℕ) : ℝ) / (((H + 1 : ℕ) : ℝ)^2)) * P a X t) := by
              rw [hnew]
        _ = ∑ t ∈ Finset.Icc 1 H, harmonicWeight (H + 1) t * P a X t := by
              rw [hshell]

/-- Exact Section 5 harmonic-weight identity after triangular reorganization in the shift variable. -/
theorem harmonic_weight_identity
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    {X H : ℕ} (hHX : H ≤ X)
    (hsq : SquareOneOnWindow a X) :
    ∃ K : ℝ, 0 ≤ K ∧
      |harmonicEnergy a X H
        - diagonalMass a X * (∑ M ∈ Finset.Icc 1 H, (1 : ℝ) / (M : ℝ))
        - 2 * ∑ t ∈ Finset.Icc 1 (H - 1), harmonicWeight H t * P a X t| ≤ K * H^2 := by
  rcases harmonic_weight_identity_preShell (a := a) ha hHX hsq with ⟨K, hK, hmain⟩
  refine ⟨K, hK, ?_⟩
  simpa [harmonicPairAccumulator_eq_weightedSum] using hmain

end HarmonicWeightExact

end FixedShiftLiouville

namespace FixedShiftLiouville

section DyadicShellEstimates

/-- A range-form telescoping identity. -/
lemma telescoping_range
    (w : ℕ → ℝ) (L n : ℕ) :
    ∑ i ∈ Finset.range n, (w (L + i) - w (L + i + 1)) = w L - w (L + n) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring_nf

/-- Telescoping the finite differences of a sequence on `Icc L (U-1)`. -/
lemma telescoping_Icc_diff
    (w : ℕ → ℝ) {L U : ℕ} (hLU : L ≤ U) (hUpos : 1 ≤ U) :
    ∑ u ∈ Finset.Icc L (U - 1), (w u - w (u + 1)) = w L - w U := by
  let n : ℕ := U - L
  have hU : U = L + n := by
    dsimp [n]
    omega
  have hpred : U - 1 + 1 = U := by omega
  rw [hU, Finset.sum_Icc_eq_sum_range]
  have hlen : L + n - 1 + 1 - L = n := by
    rw [← hU]
    rw [hpred]
  rw [hlen]
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using telescoping_range w L n

/-- The harmonic weights decrease in the shift parameter. -/
lemma harmonicWeight_monotone_step
    {H u : ℕ} (hu : u + 1 ≤ H) :
    harmonicWeight H (u + 1) ≤ harmonicWeight H u := by
  have hdiff := harmonicWeight_difference (H := H) (u := u) hu
  rw [← sub_nonneg]
  rw [hdiff]
  positivity

/-- The finite differences of the harmonic weights are nonnegative. -/
lemma harmonicWeight_difference_nonneg
    {H u : ℕ} (hu : u + 1 ≤ H) :
    0 ≤ harmonicWeight H u - harmonicWeight H (u + 1) := by
  rw [harmonicWeight_difference (H := H) (u := u) hu]
  positivity

/-- Shellwise control of the weighted quartic contribution from a uniform `Qshell` bound. -/
theorem shell_weighted_contribution_bound
    {a : ℕ → ℝ} {X H k : ℕ} {B : ℝ}
    (hB : 0 ≤ B)
    (hQ : ∀ u ∈ Finset.Icc (2 ^ k) (shellTop H k), |Qshell a X k u| ≤ B) :
    |∑ t ∈ Finset.Icc (2 ^ k) (shellTop H k), harmonicWeight H t * P a X t|
      ≤ B * harmonicWeight H (2 ^ k) := by
  by_cases hshell : 2 ^ k ≤ shellTop H k
  · have hrepr := shell_summation_by_parts (a := a) (X := X) (H := H) (k := k)
    let L : ℕ := 2 ^ k
    let U : ℕ := shellTop H k
    have hLU : L ≤ U := hshell
    have hUle : U ≤ H - 1 := by
      dsimp [U, shellTop]
      exact min_le_right _ _
    have hUpos : 1 ≤ U := le_trans Nat.one_le_two_pow hLU
    have hU1H : U + 1 ≤ H := by
      omega
    have hdiff_nonneg :
        ∀ u ∈ Finset.Icc L (U - 1), 0 ≤ harmonicWeight H u - harmonicWeight H (u + 1) := by
      intro u hu
      have huH : u + 1 ≤ H := by
        have huU : u ≤ U - 1 := (Finset.mem_Icc.mp hu).2
        omega
      exact harmonicWeight_difference_nonneg (H := H) (u := u) huH
    have hsum_abs :
        |∑ u ∈ Finset.Icc L (U - 1),
            (harmonicWeight H u - harmonicWeight H (u + 1)) * Qshell a X k u|
          ≤ B * (harmonicWeight H L - harmonicWeight H U) := by
      have h1 :
          |∑ u ∈ Finset.Icc L (U - 1),
              (harmonicWeight H u - harmonicWeight H (u + 1)) * Qshell a X k u|
            ≤ ∑ u ∈ Finset.Icc L (U - 1),
                |(harmonicWeight H u - harmonicWeight H (u + 1)) * Qshell a X k u| := by
              exact abs_sum_le_sum_abs (fun u => (harmonicWeight H u - harmonicWeight H (u + 1)) * Qshell a X k u)
      have h2 :
          ∑ u ∈ Finset.Icc L (U - 1),
              |(harmonicWeight H u - harmonicWeight H (u + 1)) * Qshell a X k u|
            ≤ ∑ u ∈ Finset.Icc L (U - 1),
                ((harmonicWeight H u - harmonicWeight H (u + 1)) * B) := by
              refine Finset.sum_le_sum ?_
              intro u hu
              have hudiff : 0 ≤ harmonicWeight H u - harmonicWeight H (u + 1) :=
                hdiff_nonneg u hu
              have huQ : |Qshell a X k u| ≤ B := by
                have hlow : 2 ^ k ≤ u := by
                  simpa [L] using (Finset.mem_Icc.mp hu).1
                have hhighU : u ≤ U := by
                  exact le_trans (Finset.mem_Icc.mp hu).2 (Nat.sub_le U 1)
                have hhigh : u ≤ shellTop H k := by
                  simpa [U] using hhighU
                exact hQ u (Finset.mem_Icc.mpr ⟨hlow, hhigh⟩)
              calc
                |(harmonicWeight H u - harmonicWeight H (u + 1)) * Qshell a X k u|
                    = (harmonicWeight H u - harmonicWeight H (u + 1)) * |Qshell a X k u| := by
                        rw [abs_mul, abs_of_nonneg hudiff]
                _ ≤ (harmonicWeight H u - harmonicWeight H (u + 1)) * B := by
                      exact mul_le_mul_of_nonneg_left huQ hudiff
      have htel :
          ∑ u ∈ Finset.Icc L (U - 1),
              ((harmonicWeight H u - harmonicWeight H (u + 1)) * B)
            = B * (harmonicWeight H L - harmonicWeight H U) := by
          calc
            ∑ u ∈ Finset.Icc L (U - 1),
                ((harmonicWeight H u - harmonicWeight H (u + 1)) * B)
                = ∑ u ∈ Finset.Icc L (U - 1),
                    (B * (harmonicWeight H u - harmonicWeight H (u + 1))) := by
                    refine Finset.sum_congr rfl ?_
                    intro u hu
                    ring
            _ = B * (∑ u ∈ Finset.Icc L (U - 1),
                    (harmonicWeight H u - harmonicWeight H (u + 1))) := by
                    rw [← Finset.mul_sum]
            _ = B * (harmonicWeight H L - harmonicWeight H U) := by
                    rw [telescoping_Icc_diff (w := harmonicWeight H) hLU hUpos]
      exact le_trans h1 (by simpa [htel] using h2)
    have hU_nonneg : 0 ≤ harmonicWeight H U := harmonicWeight_nonneg H U
    have hmono : harmonicWeight H U ≤ harmonicWeight H L := by
      have htel := telescoping_Icc_diff (w := harmonicWeight H) hLU hUpos
      have hnonneg_sum :
          0 ≤ ∑ u ∈ Finset.Icc L (U - 1), (harmonicWeight H u - harmonicWeight H (u + 1)) := by
            refine Finset.sum_nonneg ?_
            intro u hu
            exact hdiff_nonneg u hu
      nlinarith [htel, hnonneg_sum]
    have htop : |harmonicWeight H U * Qshell a X k U| ≤ B * harmonicWeight H U := by
      have hQU : |Qshell a X k U| ≤ B := hQ U (by simp [L, U, hLU])
      calc
        |harmonicWeight H U * Qshell a X k U|
            = harmonicWeight H U * |Qshell a X k U| := by
                rw [abs_mul, abs_of_nonneg hU_nonneg]
        _ ≤ harmonicWeight H U * B := by
              exact mul_le_mul_of_nonneg_left hQU hU_nonneg
        _ = B * harmonicWeight H U := by ring
    rw [hrepr]
    calc
      |harmonicWeight H U * Qshell a X k U
          + ∑ u ∈ Finset.Icc L (U - 1),
              (harmonicWeight H u - harmonicWeight H (u + 1)) * Qshell a X k u|
          ≤ |harmonicWeight H U * Qshell a X k U|
            + |∑ u ∈ Finset.Icc L (U - 1),
                (harmonicWeight H u - harmonicWeight H (u + 1)) * Qshell a X k u| := by
              exact abs_add _ _
      _ ≤ B * harmonicWeight H U + B * (harmonicWeight H L - harmonicWeight H U) := by
            exact add_le_add htop hsum_abs
      _ = B * harmonicWeight H L := by ring
      _ = B * harmonicWeight H (2 ^ k) := by rfl
  · have hlt : shellTop H k < 2 ^ k := by omega
    have hempty : Finset.Icc (2 ^ k) (shellTop H k) = ∅ := by
      exact Finset.Icc_eq_empty_of_lt hlt
    rw [hempty]
    simp
    exact mul_nonneg hB (harmonicWeight_nonneg H (2 ^ k))

/-- A scaled form of the shell contribution bound matching the dyadic local quartic scale. -/
theorem shell_weighted_contribution_bound_scaled
    {a : ℕ → ℝ} {X H k : ℕ} {δ : ℝ}
    (hδ : 0 ≤ δ)
    (hQ : ∀ u ∈ Finset.Icc (2 ^ k) (shellTop H k),
      |Qshell a X k u| ≤ δ * X * 2 ^ k) :
    |∑ t ∈ Finset.Icc (2 ^ k) (shellTop H k), harmonicWeight H t * P a X t|
      ≤ (δ * X * 2 ^ k) * harmonicWeight H (2 ^ k) := by
  exact shell_weighted_contribution_bound (a := a) (X := X) (H := H) (k := k)
    (B := δ * X * 2 ^ k) (by positivity) hQ

end DyadicShellEstimates

end FixedShiftLiouville


namespace FixedShiftLiouville

section HarmonicWeightedQuartic

/-- The harmonic series on `Icc 1 H`. -/
def harmonicSeries (H : ℕ) : ℝ :=
  ∑ M ∈ Finset.Icc 1 H, (1 : ℝ) / (M : ℝ)

/--
A direct Section 5 asymptotic input for the harmonic-weighted quartic sum at the critical scale.

This is the exact quantity that appears in the harmonic-weight identity after the shell-by-shell
reorganization. The next pass can discharge it from the local `Qshell` hypothesis.
-/
def HarmonicWeightedQuarticHyp (a : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ X₀ : ℕ, ∀ ⦃X : ℕ⦄, X₀ ≤ X →
    |∑ t ∈ Finset.Icc 1 (criticalScale X - 1),
        harmonicWeight (criticalScale X) t * P a X t|
      ≤ ε * X * criticalScale X

lemma harmonicSeries_nonneg (H : ℕ) : 0 ≤ harmonicSeries H := by
  unfold harmonicSeries
  positivity

/-- A crude but sufficient square-root bound for the harmonic series. -/
lemma harmonicSeries_bound_sqrt (H : ℕ) :
    harmonicSeries H ≤ 2 * Nat.sqrt H + 1 := by
  classical
  let s : ℕ := Nat.sqrt H
  have hsle : s ≤ H := by
    dsimp [s]
    exact Nat.sqrt_le_self H
  have hsplit :
      harmonicSeries H
        = ∑ M ∈ (Finset.Icc 1 H).filter (fun M => M ≤ s), (1 : ℝ) / (M : ℝ)
          + ∑ M ∈ (Finset.Icc 1 H).filter (fun M => ¬ M ≤ s), (1 : ℝ) / (M : ℝ) := by
    unfold harmonicSeries
    simpa using
      (Finset.sum_filter_add_sum_filter_not (s := Finset.Icc 1 H)
        (f := fun M => (1 : ℝ) / (M : ℝ)) (p := fun M => M ≤ s)).symm
  have hfirst_set :
      (Finset.Icc 1 H).filter (fun M => M ≤ s) = Finset.Icc 1 s := by
    ext M
    simp [hsle]
    omega
  have hsecond_set :
      (Finset.Icc 1 H).filter (fun M => ¬ M ≤ s) = Finset.Icc (s + 1) H := by
    ext M
    simp [hsle]
    omega
  have hfirst :
      ∑ M ∈ (Finset.Icc 1 H).filter (fun M => M ≤ s), (1 : ℝ) / (M : ℝ) ≤ s := by
    rw [hfirst_set]
    calc
      ∑ M ∈ Finset.Icc 1 s, (1 : ℝ) / (M : ℝ)
          ≤ ∑ _M ∈ Finset.Icc 1 s, (1 : ℝ) := by
            refine Finset.sum_le_sum ?_
            intro M hM
            have hM1 : 1 ≤ M := (Finset.mem_Icc.mp hM).1
            have hMreal : (1 : ℝ) ≤ M := by exact_mod_cast hM1
            have hMpos : (0 : ℝ) < M := by positivity
            have hinv : (1 : ℝ) / (M : ℝ) ≤ 1 := by
              rw [div_le_iff₀ hMpos]
              nlinarith
            simpa using hinv
      _ = s := by simp
  have htail_term :
      ∀ M ∈ Finset.Icc (s + 1) H, (1 : ℝ) / (M : ℝ) ≤ (1 : ℝ) / (s + 1 : ℝ) := by
    intro M hM
    have hMge : s + 1 ≤ M := (Finset.mem_Icc.mp hM).1
    have hspos : (0 : ℝ) < (s + 1 : ℝ) := by positivity
    have hle : (s + 1 : ℝ) ≤ M := by exact_mod_cast hMge
    exact one_div_le_one_div_of_le hspos hle
  have hsecond :
      ∑ M ∈ (Finset.Icc 1 H).filter (fun M => ¬ M ≤ s), (1 : ℝ) / (M : ℝ) ≤ s + 1 := by
    rw [hsecond_set]
    have hsum_le :
        ∑ M ∈ Finset.Icc (s + 1) H, (1 : ℝ) / (M : ℝ)
          ≤ ∑ _M ∈ Finset.Icc (s + 1) H, (1 : ℝ) / (s + 1 : ℝ) := by
            refine Finset.sum_le_sum ?_
            intro M hM
            exact htail_term M hM
    have hsq : H < (s + 1)^2 := by
      dsimp [s]
      exact Nat.lt_succ_sqrt' H
    calc
      ∑ M ∈ Finset.Icc (s + 1) H, (1 : ℝ) / (M : ℝ)
          ≤ ∑ _M ∈ Finset.Icc (s + 1) H, (1 : ℝ) / (s + 1 : ℝ) := hsum_le
      _ = ((Finset.Icc (s + 1) H).card : ℝ) / (s + 1 : ℝ) := by
            simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      _ = ((H - s : ℕ) : ℝ) / (s + 1 : ℝ) := by simp [hsle]
      _ ≤ s + 1 := by
            have hspos : (0 : ℝ) < (s + 1 : ℝ) := by positivity
            have hsq' : (H : ℝ) < (s + 1 : ℝ)^2 := by exact_mod_cast hsq
            have hsle' : (s : ℝ) ≤ H := by exact_mod_cast hsle
            rw [Nat.cast_sub hsle]
            rw [div_le_iff₀ hspos]
            nlinarith
  rw [hsplit]
  nlinarith

/-- The harmonic main term is negligible compared with `X * criticalScale X`. -/
lemma harmonicSeries_small_at_criticalScale :
    ∀ ε > 0, ∃ X₀ : ℕ, ∀ ⦃X : ℕ⦄, X₀ ≤ X ->
      harmonicSeries (criticalScale X) ≤ ε * criticalScale X := by
  intro ε hε
  rcases criticalScale_sublinear (ε / 4) (by positivity) with ⟨Y₀, hY₀⟩
  rcases exists_nat_gt (4 / ε) with ⟨q, hq⟩
  have hqpos : 0 < q := by
    have h4pos : (0 : ℝ) < 4 / ε := div_pos (by norm_num) hε
    exact Nat.cast_pos.mp (lt_trans h4pos hq)
  have hq1 : 1 ≤ q := Nat.succ_le_of_lt (Nat.cast_pos.mp hqpos)
  rcases eventually_criticalScale_ge Y₀ with ⟨X₁, hX₁⟩
  rcases eventually_criticalScale_ge q with ⟨X₂, hX₂⟩
  refine ⟨max X₁ X₂, ?_⟩
  intro X hX
  have hXY : Y₀ ≤ criticalScale X := hX₁ (le_trans (le_max_left _ _) hX)
  have hXq : q ≤ criticalScale X := hX₂ (le_trans (le_max_right _ _) hX)
  have hinner : (criticalScale (criticalScale X) : ℝ) ≤ (ε / 4) * criticalScale X := by
    exact hY₀ hXY
  have hone : (1 : ℝ) ≤ (ε / 2) * criticalScale X := by
    have hq' : (q : ℝ) ≤ criticalScale X := by exact_mod_cast hXq
    have hlt : 4 / ε < (criticalScale X : ℝ) := lt_of_lt_of_le hq hq'
    have hmul : 4 < ε * (criticalScale X : ℝ) := by
      have htmp : 4 < (criticalScale X : ℝ) * ε := by
        rwa [div_lt_iff₀ hε] at hlt
      nlinarith
    nlinarith
  calc
    harmonicSeries (criticalScale X)
        ≤ 2 * criticalScale (criticalScale X) + 1 := by
              simpa [criticalScale] using harmonicSeries_bound_sqrt (criticalScale X)
    _ ≤ ε * criticalScale X := by
          nlinarith

/-- The quadratic boundary loss `H²` is negligible at the critical scale. -/
lemma criticalScale_sq_small :
    ∀ K ε : ℝ, ε > 0 → ∃ X₀ : ℕ, ∀ ⦃X : ℕ⦄, X₀ ≤ X ->
      K * (criticalScale X : ℝ)^2 ≤ ε * X * criticalScale X := by
  intro K ε hε
  by_cases hK : K ≤ 0
  · refine ⟨1, ?_⟩
    intro X hX
    have hnonneg : 0 ≤ ε * X * criticalScale X := by positivity
    nlinarith
  · have hKpos : 0 < K := by linarith
    rcases criticalScale_sublinear (ε / K) (div_pos hε hKpos) with ⟨X₀, hX₀⟩
    refine ⟨X₀, ?_⟩
    intro X hX
    have hmain : (criticalScale X : ℝ) ≤ (ε / K) * X := hX₀ hX
    have hmainK : K * (criticalScale X : ℝ) ≤ ε * X := by
      have hmul := mul_le_mul_of_nonneg_left hmain (le_of_lt hKpos)
      field_simp [ne_of_gt hKpos] at hmul
      simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
    have hHnonneg : 0 ≤ (criticalScale X : ℝ) := by positivity
    nlinarith

/-- A uniform form of the harmonic-weight identity with an `O(H²)` constant independent of `X,H`. -/
theorem harmonic_weight_identity_uniform
    {a : ℕ → ℝ}
    (ha : BoundedByOne a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ X H : ℕ, H ≤ X → SquareOneOnWindow a X →
      |harmonicEnergy a X H
        - diagonalMass a X * harmonicSeries H
        - 2 * ∑ t ∈ Finset.Icc 1 (H - 1), harmonicWeight H t * P a X t| ≤ K * H^2 := by
  rcases fejer_representation (a := a) ha with ⟨K, hK, hfej⟩
  refine ⟨K, hK, ?_⟩
  intro X H hHX hsq
  have hexpand :
      harmonicEnergy a X H
        - diagonalMass a X * harmonicSeries H
        - 2 * harmonicPairAccumulator a X H
        = ∑ M ∈ Finset.Icc 1 H,
            (E a X M / (M : ℝ)^2 - fejerMainTerm a X (M - 1) / (M : ℝ)^2) := by
    unfold harmonicEnergy harmonicSeries
    have hmainCoeff := harmonicMainCoefficient_expand a X H
    calc
      (∑ M ∈ Finset.Icc 1 H, E a X M / (M : ℝ)^2)
        - diagonalMass a X * (∑ M ∈ Finset.Icc 1 H, (1 : ℝ) / (M : ℝ))
        - 2 * harmonicPairAccumulator a X H
          = (∑ M ∈ Finset.Icc 1 H, E a X M / (M : ℝ)^2)
            - (diagonalMass a X * (∑ M ∈ Finset.Icc 1 H, (1 : ℝ) / (M : ℝ))
                + 2 * harmonicPairAccumulator a X H) := by ring
      _ = (∑ M ∈ Finset.Icc 1 H, E a X M / (M : ℝ)^2)
            - (∑ M ∈ Finset.Icc 1 H, fejerMainTerm a X (M - 1) / (M : ℝ)^2) := by
              rw [hmainCoeff]
      _ = ∑ M ∈ Finset.Icc 1 H,
            (E a X M / (M : ℝ)^2 - fejerMainTerm a X (M - 1) / (M : ℝ)^2) := by
              rw [← Finset.sum_sub_distrib]
  have hpre :
      |harmonicEnergy a X H
        - diagonalMass a X * harmonicSeries H
        - 2 * harmonicPairAccumulator a X H| ≤ K * H^2 := by
    rw [hexpand]
    calc
      |∑ M ∈ Finset.Icc 1 H,
          (E a X M / (M : ℝ)^2 - fejerMainTerm a X (M - 1) / (M : ℝ)^2)|
          ≤ ∑ M ∈ Finset.Icc 1 H,
              |E a X M / (M : ℝ)^2 - fejerMainTerm a X (M - 1) / (M : ℝ)^2| := by
                exact abs_sum_le_sum_abs (fun M => E a X M / (M : ℝ)^2 - fejerMainTerm a X (M - 1) / (M : ℝ)^2)
      _ ≤ ∑ M ∈ Finset.Icc 1 H, K * M := by
            refine Finset.sum_le_sum ?_
            intro M hM
            have hM1 : 1 ≤ M := (Finset.mem_Icc.mp hM).1
            have hMleH : M ≤ H := (Finset.mem_Icc.mp hM).2
            have hpredleX : M - 1 ≤ X := by
              exact le_trans (le_trans (Nat.sub_le M 1) hMleH) hHX
            have hmain := hfej X (M - 1) hpredleX hsq
            have hM0 : (M : ℝ) ≠ 0 := by
              exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hM1))
            have hM2 : 0 ≤ (M : ℝ)^2 := sq_nonneg (M : ℝ)
            have hdiv :
                |(E a X M - fejerMainTerm a X (M - 1)) / (M : ℝ)^2|
                  ≤ (K * (M : ℝ)^3) / (M : ℝ)^2 := by
              have hrew : E a X ((M - 1) + 1) = E a X M := by
                congr
                exact Nat.sub_add_cancel hM1
              rw [hrew] at hmain
              have hpow : (((M - 1 : ℕ) : ℝ) + 1) = (M : ℝ) := by
                exact_mod_cast (Nat.sub_add_cancel hM1)
              rw [hpow] at hmain
              rw [abs_div, abs_of_nonneg hM2]
              exact div_le_div_of_nonneg_right hmain hM2
            have habs_div :
                |E a X M / (M : ℝ)^2 - fejerMainTerm a X (M - 1) / (M : ℝ)^2|
                  = |(E a X M - fejerMainTerm a X (M - 1)) / (M : ℝ)^2| := by
              congr 1
              field_simp [hM0]
            rw [habs_div]
            calc
              |(E a X M - fejerMainTerm a X (M - 1)) / (M : ℝ)^2|
                  ≤ (K * (M : ℝ)^3) / (M : ℝ)^2 := hdiv
              _ = K * M := by
                  field_simp [hM0]
      _ = K * (∑ M ∈ Finset.Icc 1 H, (M : ℝ)) := by
            rw [← mul_sum (s := Finset.Icc 1 H) (c := K) (f := fun M => (M : ℝ))]
      _ ≤ K * H^2 := by
            exact mul_le_mul_of_nonneg_left (sum_Icc_cast_id_le_sq H) hK
  simpa [harmonicSeries, harmonicPairAccumulator_eq_weightedSum] using hpre

/--
Section 5 reduction from the harmonic-weighted quartic form to the positive multiscale bound.

This is the last step after the exact harmonic identity has been established. The remaining work in
this section is to deduce `HarmonicWeightedQuarticHyp` from the shellwise `Qshell` hypothesis.
-/
theorem positiveMultiscale_of_harmonicWeightedQuartic
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    (hsqev : EventuallySquareOne a)
    (hquartic : HarmonicWeightedQuarticHyp a) :
    PositiveMultiscaleHyp a := by
  rcases harmonic_weight_identity_uniform (a := a) ha with ⟨K, hK, hident⟩
  intro ε hε
  rcases hquartic (ε / 8) (by positivity) with ⟨X₁, hX₁⟩
  rcases hsqev with ⟨X₂, hX₂⟩
  rcases harmonicSeries_small_at_criticalScale (ε / 4) (by positivity) with ⟨X₃, hX₃⟩
  rcases criticalScale_sq_small K (ε / 4) (by positivity) with ⟨X₄, hX₄⟩
  refine ⟨max X₁ (max X₂ (max X₃ X₄)), ?_⟩
  intro X hX
  let H : ℕ := criticalScale X
  have hX₁' : X₁ ≤ X := le_trans (le_max_left _ _) hX
  have htail : max X₂ (max X₃ X₄) ≤ X := le_trans (le_max_right _ _) hX
  have hX₂' : X₂ ≤ X := le_trans (le_max_left _ _) htail
  have htail2 : max X₃ X₄ ≤ X := le_trans (le_max_right _ _) htail
  have hX₃' : X₃ ≤ X := le_trans (le_max_left _ _) htail2
  have hX₄' : X₄ ≤ X := le_trans (le_max_right _ _) htail2
  have hHX : H ≤ X := criticalScale_le_self X
  have hsq : SquareOneOnWindow a X := hX₂ hX₂'
  have hdiag : diagonalMass a X = X := diagonalMass_eq_X_of_squareOne (a := a) (X := X) hsq
  have hquart :
      |∑ t ∈ Finset.Icc 1 (H - 1), harmonicWeight H t * P a X t|
        ≤ (ε / 8) * X * H := by
    simpa [H] using hX₁ hX₁'
  have hmainTerm : X * harmonicSeries H ≤ (ε / 4) * X * H := by
    have hhs : harmonicSeries H ≤ (ε / 4) * H := by simpa [H] using hX₃ hX₃'
    nlinarith
  have herror : K * (H : ℝ)^2 ≤ (ε / 4) * X * H := by
    simpa [H] using hX₄ hX₄'
  have hident' := hident X H hHX hsq
  calc
    harmonicEnergy a X H
        ≤ |harmonicEnergy a X H
            - diagonalMass a X * harmonicSeries H
            - 2 * ∑ t ∈ Finset.Icc 1 (H - 1), harmonicWeight H t * P a X t|
          + |diagonalMass a X * harmonicSeries H|
          + |2 * ∑ t ∈ Finset.Icc 1 (H - 1), harmonicWeight H t * P a X t| := by
              let A := harmonicEnergy a X H
                - diagonalMass a X * harmonicSeries H
                - 2 * ∑ t ∈ Finset.Icc 1 (H - 1), harmonicWeight H t * P a X t
              let B := diagonalMass a X * harmonicSeries H
              let C := 2 * ∑ t ∈ Finset.Icc 1 (H - 1), harmonicWeight H t * P a X t
              have hsplit : harmonicEnergy a X H = A + B + C := by
                dsimp [A, B, C]
                ring
              have htri1 : |A + B| ≤ |A| + |B| := abs_add A B
              have htri2 : |A + B + C| ≤ |A + B| + |C| := abs_add (A + B) C
              calc
                harmonicEnergy a X H ≤ |harmonicEnergy a X H| := le_abs_self _
                _ = |A + B + C| := by rw [hsplit]
                _ ≤ |A| + |B| + |C| := by nlinarith
    _ ≤ K * (H : ℝ)^2 + X * harmonicSeries H + 2 * |∑ t ∈ Finset.Icc 1 (H - 1), harmonicWeight H t * P a X t| := by
          rw [hdiag]
          have hidentX :
              |harmonicEnergy a X H - X * harmonicSeries H
                  - 2 * ∑ t ∈ Finset.Icc 1 (H - 1), harmonicWeight H t * P a X t| ≤ K * H^2 := by
                simpa [hdiag] using hident'
          have hHSnonneg : 0 ≤ harmonicSeries H := by
            unfold harmonicSeries
            positivity
          have habs_main : |X * harmonicSeries H| = X * harmonicSeries H := by
            rw [abs_of_nonneg]
            exact mul_nonneg (by positivity) hHSnonneg
          have habs_two : |2 * ∑ t ∈ Finset.Icc 1 (H - 1), harmonicWeight H t * P a X t|
              = 2 * |∑ t ∈ Finset.Icc 1 (H - 1), harmonicWeight H t * P a X t| := by
                rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
          rw [habs_main, habs_two]
          nlinarith [hidentX]
    _ ≤ (ε / 4) * X * H + (ε / 4) * X * H + 2 * ((ε / 8) * X * H) := by
          gcongr
    _ ≤ ε * X * H := by
          have hXHnonneg : 0 ≤ (X : ℝ) * H := by positivity
          nlinarith [mul_nonneg (le_of_lt hε) hXHnonneg]

end HarmonicWeightedQuartic

end FixedShiftLiouville

namespace FixedShiftLiouville

section DyadicLocalQuarticAggregation

/-- Epsilon-form dyadic local quartic control on every shell up to the critical scale. -/
def DyadicLocalQuarticHyp (a : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ X₀ : ℕ, ∀ ⦃X : ℕ⦄, X₀ ≤ X ->
    ∀ k ∈ Finset.range (criticalScale X),
      ∀ u ∈ Finset.Icc (2 ^ k) (shellTop (criticalScale X) k),
        |Qshell a X k u| ≤ ε * X * 2 ^ k

/-- The Section 5 dyadic shell weighted sum before flattening the shell partition. -/
def dyadicShellWeightedSum (a : ℕ → ℝ) (X H : ℕ) : ℝ :=
  ∑ k ∈ Finset.range H,
    ∑ t ∈ Finset.Icc (2 ^ k) (shellTop H k), harmonicWeight H t * P a X t

lemma two_pow_mono {m n : ℕ} (h : m ≤ n) : 2 ^ m ≤ 2 ^ n := by
  induction h with
  | refl => simp
  | @step n h ih =>
      calc
        2 ^ m ≤ 2 ^ n := ih
        _ ≤ 2 ^ (n + 1) := by
            rw [pow_succ]
            have hnonneg : 0 ≤ 2 ^ n := by positivity
            nlinarith

lemma self_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        n + 1 ≤ 2 ^ n + 1 := Nat.succ_le_succ ih
        _ ≤ 2 ^ n + 2 ^ n := by
            have hpow : 1 ≤ 2 ^ n := Nat.one_le_two_pow
            omega
        _ = 2 ^ (n + 1) := by rw [pow_succ]; ring

lemma sum_range_two_pow (n : ℕ) :
    ∑ k ∈ Finset.range n, ((2 ^ k : ℕ) : ℝ) = (2 ^ n : ℝ) - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      norm_num [pow_succ]
      ring

/-- For every positive integer `m`, some power of two lies in `[m, 2m)`. -/
lemma exists_two_pow_ceiling :
    ∀ m : ℕ, 1 ≤ m → ∃ j : ℕ, m ≤ 2 ^ j ∧ 2 ^ j < 2 * m
  | 0, hm => by cases hm
  | 1, _ => ⟨0, by simp, by simp⟩
  | m + 1 + 1, _ => by
      rcases exists_two_pow_ceiling (m + 1) (by omega) with ⟨j, hj₁, hj₂⟩
      by_cases hcase : m + 2 ≤ 2 ^ j
      · exact ⟨j, hcase, by nlinarith [hj₂]⟩
      · have hEq : 2 ^ j = m + 1 := by omega
        refine ⟨j + 1, ?_, ?_⟩
        · rw [pow_succ, hEq]
          omega
        · rw [pow_succ, hEq]
          omega

/-- A truncated geometric series of powers of two is bounded by twice the cutoff. -/
lemma sum_two_pow_filter_lt (m H : ℕ) (hm : 1 ≤ m) :
    ∑ k ∈ Finset.range H, (if 2 ^ k < m then ((2 ^ k : ℕ) : ℝ) else 0) ≤ 2 * m := by
  rcases exists_two_pow_ceiling m hm with ⟨j, hj₁, hj₂⟩
  have hsubset :
      (Finset.range H).filter (fun k => 2 ^ k < m) ⊆ Finset.range j := by
    intro k hk
    have hkltm : 2 ^ k < m := (Finset.mem_filter.mp hk).2
    have hkj : k < j := by
      by_contra hnot
      have hjk : j ≤ k := by omega
      have hpow : 2 ^ j ≤ 2 ^ k := two_pow_mono hjk
      exact (not_le_of_gt hkltm) (le_trans hj₁ hpow)
    simpa using hkj
  calc
    ∑ k ∈ Finset.range H, (if 2 ^ k < m then ((2 ^ k : ℕ) : ℝ) else 0)
        = ∑ k ∈ ((Finset.range H).filter (fun k => 2 ^ k < m)), ((2 ^ k : ℕ) : ℝ) := by
            rw [Finset.sum_filter]
    _ ≤ ∑ k ∈ Finset.range j, ((2 ^ k : ℕ) : ℝ) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
          intro k hk hknot
          positivity
    _ = (2 ^ j : ℝ) - 1 := sum_range_two_pow j
    _ ≤ 2 * m := by
          have hj₂r : (2 : ℝ)^j < 2 * (m : ℝ) := by exact_mod_cast hj₂
          have hminus : (2 : ℝ)^j - 1 ≤ (2 : ℝ)^j := by linarith
          exact le_trans hminus (le_of_lt hj₂r)

/-- The dyadic shell coefficients have total budget `O(H)`. -/
lemma dyadicShellCoefficient_bound (H : ℕ) :
    ∑ k ∈ Finset.range H, ((2 ^ k : ℕ) : ℝ) * harmonicWeight H (2 ^ k) ≤ 2 * H := by
  have hstep :
      ∑ k ∈ Finset.range H, ((2 ^ k : ℕ) : ℝ) * harmonicWeight H (2 ^ k)
        ≤ ∑ k ∈ Finset.range H, ∑ M ∈ Finset.Icc (2 ^ k + 1) H, ((2 ^ k : ℕ) : ℝ) / (M : ℝ) := by
    refine Finset.sum_le_sum ?_
    intro k hk
    have hnonneg : 0 ≤ ((2 ^ k : ℕ) : ℝ) := by positivity
    calc
      ((2 ^ k : ℕ) : ℝ) * harmonicWeight H (2 ^ k)
          ≤ ((2 ^ k : ℕ) : ℝ) * (∑ M ∈ Finset.Icc (2 ^ k + 1) H, (1 : ℝ) / (M : ℝ)) := by
              exact mul_le_mul_of_nonneg_left (harmonicWeight_le_harmonicTail H (2 ^ k)) hnonneg
      _ = ∑ M ∈ Finset.Icc (2 ^ k + 1) H, ((2 ^ k : ℕ) : ℝ) / (M : ℝ) := by
            rw [mul_sum]
            refine Finset.sum_congr rfl ?_
            intro M hM
            ring
  have hreindex :
      ∑ k ∈ Finset.range H, ∑ M ∈ Finset.Icc (2 ^ k + 1) H, ((2 ^ k : ℕ) : ℝ) / (M : ℝ)
        = ∑ M ∈ Finset.Icc 1 H,
            ∑ k ∈ Finset.range H, (if 2 ^ k < M then ((2 ^ k : ℕ) : ℝ) / (M : ℝ) else 0) := by
    calc
      ∑ k ∈ Finset.range H, ∑ M ∈ Finset.Icc (2 ^ k + 1) H, ((2 ^ k : ℕ) : ℝ) / (M : ℝ)
          = ∑ k ∈ Finset.range H, ∑ M ∈ Finset.Icc 1 H,
              (if 2 ^ k < M then ((2 ^ k : ℕ) : ℝ) / (M : ℝ) else 0) := by
                refine Finset.sum_congr rfl ?_
                intro k hk
                rw [show Finset.Icc (2 ^ k + 1) H = (Finset.Icc 1 H).filter (fun M => 2 ^ k < M) by
                  ext M
                  have hpowpos : 1 ≤ 2 ^ k := Nat.one_le_two_pow
                  simp [Finset.mem_Icc]
                  omega]
                rw [Finset.sum_filter]
      _ = ∑ M ∈ Finset.Icc 1 H,
            ∑ k ∈ Finset.range H, (if 2 ^ k < M then ((2 ^ k : ℕ) : ℝ) / (M : ℝ) else 0) := by
              rw [Finset.sum_comm]
  have hinner :
      ∀ M ∈ Finset.Icc 1 H,
        ∑ k ∈ Finset.range H, (if 2 ^ k < M then ((2 ^ k : ℕ) : ℝ) / (M : ℝ) else 0) ≤ 2 := by
    intro M hM
    have hM1 : 1 ≤ M := (Finset.mem_Icc.mp hM).1
    have hM0 : (M : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hM1))
    have hfactor :
        ∑ k ∈ Finset.range H, (if 2 ^ k < M then ((2 ^ k : ℕ) : ℝ) / (M : ℝ) else 0)
          = (∑ k ∈ Finset.range H, (if 2 ^ k < M then ((2 ^ k : ℕ) : ℝ) else 0)) / (M : ℝ) := by
            rw [div_eq_mul_inv]
            rw [sum_mul]
            refine Finset.sum_congr rfl ?_
            intro k hk
            split_ifs <;> ring
    rw [hfactor]
    have hsum := sum_two_pow_filter_lt M H hM1
    have hMpos : (0 : ℝ) < (M : ℝ) := by positivity
    calc
      (∑ k ∈ Finset.range H, (if 2 ^ k < M then ((2 ^ k : ℕ) : ℝ) else 0)) / (M : ℝ)
          ≤ (2 * (M : ℝ)) / (M : ℝ) := by
            exact div_le_div_of_nonneg_right hsum (le_of_lt hMpos)
      _ = 2 := by
            field_simp [hM0]
  calc
    ∑ k ∈ Finset.range H, ((2 ^ k : ℕ) : ℝ) * harmonicWeight H (2 ^ k)
        ≤ ∑ k ∈ Finset.range H, ∑ M ∈ Finset.Icc (2 ^ k + 1) H, ((2 ^ k : ℕ) : ℝ) / (M : ℝ) := hstep
    _ = ∑ M ∈ Finset.Icc 1 H,
          ∑ k ∈ Finset.range H, (if 2 ^ k < M then ((2 ^ k : ℕ) : ℝ) / (M : ℝ) else 0) := hreindex
    _ ≤ ∑ _M ∈ Finset.Icc 1 H, (2 : ℝ) := by
          refine Finset.sum_le_sum ?_
          intro M hM
          exact hinner M hM
    _ = 2 * H := by
          simp
          ring

/-- Shellwise quartic cancellation obtained directly from the local `Qshell` hypothesis. -/
theorem dyadicShellWeightedSum_small_of_dyadicLocalQuartic
    {a : ℕ → ℝ}
    (hdyadic : DyadicLocalQuarticHyp a) :
    ∀ ε > 0, ∃ X₀ : ℕ, ∀ ⦃X : ℕ⦄, X₀ ≤ X ->
      |dyadicShellWeightedSum a X (criticalScale X)| ≤ ε * X * criticalScale X := by
  intro ε hε
  rcases hdyadic (ε / 2) (by positivity) with ⟨X₀, hX₀⟩
  refine ⟨X₀, ?_⟩
  intro X hX
  let H : ℕ := criticalScale X
  have hshell :
      ∀ k ∈ Finset.range H,
        |∑ t ∈ Finset.Icc (2 ^ k) (shellTop H k), harmonicWeight H t * P a X t|
          ≤ ((ε / 2) * X * 2 ^ k) * harmonicWeight H (2 ^ k) := by
    intro k hk
    exact shell_weighted_contribution_bound_scaled (a := a) (X := X) (H := H) (k := k)
      (δ := ε / 2) (by positivity) (hX₀ hX k (by simpa [H] using hk))
  have hsum_abs :
      |dyadicShellWeightedSum a X H|
        ≤ ∑ k ∈ Finset.range H,
            |∑ t ∈ Finset.Icc (2 ^ k) (shellTop H k), harmonicWeight H t * P a X t| := by
    unfold dyadicShellWeightedSum
    exact abs_sum_le_sum_abs (fun k => ∑ t ∈ Finset.Icc (2 ^ k) (shellTop H k), harmonicWeight H t * P a X t)
  have hmajor :
      ∑ k ∈ Finset.range H,
          |∑ t ∈ Finset.Icc (2 ^ k) (shellTop H k), harmonicWeight H t * P a X t|
        ≤ ∑ k ∈ Finset.range H, (((ε / 2) * X * 2 ^ k) * harmonicWeight H (2 ^ k)) := by
    refine Finset.sum_le_sum ?_
    intro k hk
    exact hshell k hk
  have hbudget := dyadicShellCoefficient_bound H
  calc
    |dyadicShellWeightedSum a X H|
        ≤ ∑ k ∈ Finset.range H,
            |∑ t ∈ Finset.Icc (2 ^ k) (shellTop H k), harmonicWeight H t * P a X t| := hsum_abs
    _ ≤ ∑ k ∈ Finset.range H, (((ε / 2) * X * 2 ^ k) * harmonicWeight H (2 ^ k)) := hmajor
    _ = ((ε / 2) * X) * 
          (∑ k ∈ Finset.range H, ((2 ^ k : ℕ) : ℝ) * harmonicWeight H (2 ^ k)) := by
            rw [mul_sum]
            refine Finset.sum_congr rfl ?_
            intro k hk
            norm_num
            ring
    _ ≤ ((ε / 2) * X) * (2 * H) := by
          gcongr
    _ = ε * X * H := by ring

/-- The shell-form quartic bound produced by dyadic local quartic control. -/
def DyadicShellWeightedQuarticHyp (a : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ X₀ : ℕ, ∀ ⦃X : ℕ⦄, X₀ ≤ X ->
    |dyadicShellWeightedSum a X (criticalScale X)| ≤ ε * X * criticalScale X

theorem dyadicShellWeightedQuartic_of_dyadicLocalQuartic
    {a : ℕ → ℝ}
    (hdyadic : DyadicLocalQuarticHyp a) :
    DyadicShellWeightedQuarticHyp a := by
  exact dyadicShellWeightedSum_small_of_dyadicLocalQuartic hdyadic

end DyadicLocalQuarticAggregation

end FixedShiftLiouville


namespace FixedShiftLiouville

section DyadicShellFlattening

/-- Every dyadic shell sits inside the global interval `[1,H-1]`. -/
lemma shell_subset_interval (H k : ℕ) :
    Finset.Icc (2 ^ k) (shellTop H k) ⊆ Finset.Icc 1 (H - 1) := by
  intro t ht
  rcases Finset.mem_Icc.mp ht with ⟨htlow, hthigh⟩
  refine Finset.mem_Icc.mpr ?_
  constructor
  · have hpow : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    exact le_trans hpow htlow
  · exact le_trans hthigh (min_le_right _ _)

/--
Each `t ∈ [1,H-1]` lies in a unique dyadic shell among `k = 0, …, H-1`.

This is the exact combinatorial partition needed to flatten the shellwise quartic sum back to the
single harmonic-weighted interval sum.
-/
lemma exists_unique_dyadic_shell
    {H t : ℕ} (ht1 : 1 ≤ t) (htH : t ≤ H - 1) :
    ∃! k : ℕ, k ∈ Finset.range H ∧ t ∈ Finset.Icc (2 ^ k) (shellTop H k) := by
  rcases exists_two_pow_ceiling (t + 1) (by omega) with ⟨j, hj₁, hj₂⟩
  have hjpos : 1 ≤ j := by
    have htwo : 2 ≤ t + 1 := by omega
    have hpow : 2 ≤ 2 ^ j := le_trans htwo hj₁
    cases j with
    | zero =>
        simp at hpow
    | succ j =>
        exact Nat.succ_le_succ (Nat.zero_le _)
  refine ⟨j - 1, ?_, ?_⟩
  · have hpow_lt : 2 ^ (j - 1) < t + 1 := by
      have hrew : j = (j - 1) + 1 := by omega
      rw [hrew, pow_succ] at hj₂
      omega
    have hpow_le_t : 2 ^ (j - 1) ≤ t := by
      omega
    have hkltH : j - 1 < H := by
      have hkself : j - 1 ≤ 2 ^ (j - 1) := self_le_two_pow (j - 1)
      omega
    refine ⟨by simpa using hkltH, ?_⟩
    refine Finset.mem_Icc.mpr ?_
    constructor
    · exact hpow_le_t
    · unfold shellTop
      have htop₁ : t ≤ 2 ^ ((j - 1) + 1) - 1 := by
        have hrew : j = (j - 1) + 1 := by omega
        rw [hrew] at hj₁
        omega
      have htop₂ : t ≤ H - 1 := htH
      exact le_min htop₁ htop₂
  · intro k hk
    rcases hk with ⟨hkH, hmem⟩
    rcases Finset.mem_Icc.mp hmem with ⟨hklo, hkhi⟩
    have hktop : shellTop H k ≤ 2 ^ (k + 1) - 1 := min_le_left _ _
    have hkhi' : t < 2 ^ (k + 1) := by
      omega
    have hpow_lt : 2 ^ (j - 1) < t + 1 := by
      have hrew : j = (j - 1) + 1 := by omega
      rw [hrew, pow_succ] at hj₂
      omega
    have hjlo : 2 ^ (j - 1) ≤ t := by
      omega
    have hjhi : t < 2 ^ j := by
      omega
    have hkeq : k = j - 1 := by
      by_contra hne
      have hlt_or_gt : k < j - 1 ∨ j - 1 < k := by omega
      cases hlt_or_gt with
      | inl hlt =>
          have hpow : 2 ^ (k + 1) ≤ 2 ^ (j - 1) := by
            exact two_pow_mono (by omega)
          omega
      | inr hgt =>
          have hpow : 2 ^ j ≤ 2 ^ k := by
            have hle : j ≤ k := by omega
            exact two_pow_mono hle
          omega
    exact hkeq

/-- Flattening the dyadic shell decomposition back to the single harmonic-weighted interval sum. -/
theorem dyadicShellWeightedSum_eq_interval_sum
    (a : ℕ → ℝ) (X H : ℕ) :
    dyadicShellWeightedSum a X H
      = ∑ t ∈ Finset.Icc 1 (H - 1), harmonicWeight H t * P a X t := by
  classical
  let f : ℕ → ℝ := fun t => harmonicWeight H t * P a X t
  calc
    dyadicShellWeightedSum a X H
        = ∑ k ∈ Finset.range H,
            ∑ t ∈ Finset.Icc 1 (H - 1),
              if t ∈ Finset.Icc (2 ^ k) (shellTop H k) then f t else 0 := by
            unfold dyadicShellWeightedSum
            refine Finset.sum_congr rfl ?_
            intro k hk
            have hsub : Finset.Icc (2 ^ k) (shellTop H k) ⊆ Finset.Icc 1 (H - 1) :=
              shell_subset_interval H k
            have hfilter :
                (Finset.Icc 1 (H - 1)).filter
                    (fun t => t ∈ Finset.Icc (2 ^ k) (shellTop H k))
                  = Finset.Icc (2 ^ k) (shellTop H k) := by
              ext t
              constructor
              · intro ht
                exact (Finset.mem_filter.mp ht).2
              · intro ht
                exact Finset.mem_filter.mpr ⟨hsub ht, ht⟩
            rw [← hfilter]
            rw [Finset.sum_filter]
            refine Finset.sum_congr rfl ?_
            intro t ht
            by_cases hs : t ∈ Finset.Icc (2 ^ k) (shellTop H k)
            · have hscond : 2 ^ k ≤ t ∧ t ≤ shellTop H k := Finset.mem_Icc.mp hs
              have hIcond : 1 ≤ t ∧ t ≤ H - 1 := Finset.mem_Icc.mp ht
              simp [f, hscond, hIcond]
            · have hscond : ¬ (2 ^ k ≤ t ∧ t ≤ shellTop H k) := by
                intro hpair
                exact hs (Finset.mem_Icc.mpr hpair)
              simp [f, hscond]
    _ = ∑ t ∈ Finset.Icc 1 (H - 1),
          ∑ k ∈ Finset.range H,
            if t ∈ Finset.Icc (2 ^ k) (shellTop H k) then f t else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ t ∈ Finset.Icc 1 (H - 1), f t := by
          refine Finset.sum_congr rfl ?_
          intro t ht
          rcases Finset.mem_Icc.mp ht with ⟨ht1, htH⟩
          rcases exists_unique_dyadic_shell (H := H) ht1 htH with ⟨k₀, hk₀, huniq⟩
          rw [Finset.sum_eq_single k₀]
          · simp [hk₀.1, hk₀.2, f]
          · intro k hk hkne
            have hnot : ¬ t ∈ Finset.Icc (2 ^ k) (shellTop H k) := by
              intro hmem
              exact hkne (huniq k ⟨hk, hmem⟩)
            simp [hnot, f]
          · intro hknot
            exact False.elim (hknot hk₀.1)
    _ = ∑ t ∈ Finset.Icc 1 (H - 1), harmonicWeight H t * P a X t := by
          rfl

/-- The shell-form quartic hypothesis is exactly the harmonic-weighted quartic hypothesis. -/
theorem harmonicWeightedQuartic_of_dyadicShellWeightedQuartic
    {a : ℕ → ℝ}
    (hshell : DyadicShellWeightedQuarticHyp a) :
    HarmonicWeightedQuarticHyp a := by
  intro ε hε
  rcases hshell ε hε with ⟨X₀, hX₀⟩
  refine ⟨X₀, ?_⟩
  intro X hX
  simpa [dyadicShellWeightedSum_eq_interval_sum] using hX₀ hX

/--
Section 5 theorem: dyadic local quartic control implies the positive multiscale hypothesis.

This closes the shellwise summation-by-parts argument by flattening the dyadic shell partition back
to the single harmonic-weighted quartic sum.
-/
theorem positiveMultiscale_of_dyadicLocalQuartic
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    (hsqev : EventuallySquareOne a)
    (hdyadic : DyadicLocalQuarticHyp a) :
    PositiveMultiscaleHyp a := by
  have hshell : DyadicShellWeightedQuarticHyp a :=
    dyadicShellWeightedQuartic_of_dyadicLocalQuartic hdyadic
  have hquartic : HarmonicWeightedQuarticHyp a :=
    harmonicWeightedQuartic_of_dyadicShellWeightedQuartic hshell
  exact positiveMultiscale_of_harmonicWeightedQuartic ha hsqev hquartic

/--
Section 5 criterion, combined with the completed Section 4 coefficient bridge.

The genuinely shellwise part of the argument is now closed: dyadic local quartic control implies the
positive multiscale hypothesis. To recover the global prefix cancellation conclusion we feed that
output into the Section 4 coefficient-level positive domination theorem.
-/
theorem dyadic_local_quartic_criterion
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    (hsqev : EventuallySquareOne a)
    (hdom : PositiveDominationCoefficient a)
    (hdyadic : DyadicLocalQuarticHyp a) :
    PrefixLittleO a := by
  have hmulti : PositiveMultiscaleHyp a :=
    positiveMultiscale_of_dyadicLocalQuartic ha hsqev hdyadic
  exact positive_multiscale_criterion_positiveDomination ha hsqev hdom hmulti

end DyadicShellFlattening

end FixedShiftLiouville


namespace FixedShiftLiouville

section FirstMoment

/-- Section 6 first-moment hypothesis, written directly at the critical scale. -/
def FirstMomentHyp (a : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ X₀ : ℕ, ∀ ⦃X M : ℕ⦄, X₀ ≤ X →
    M ∈ Finset.Icc 1 (criticalScale X) →
      ∑ x ∈ Finset.Icc X (2 * X - M), |B a x M| ≤ ε * X * M

/--
The absolute first-moment hypothesis directly implies the critical short-block energy hypothesis.
This is the formal version of the elementary estimate
`∑ |B_H|^2 ≤ H ∑ |B_H|`, using `|B_H| ≤ H`.
-/
theorem criticalShortBlock_of_firstMoment
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    (hfirst : FirstMomentHyp a) :
    CriticalShortBlockHyp a := by
  intro ε hε
  rcases hfirst ε hε with ⟨X₁, hX₁⟩
  refine ⟨max X₁ 1, ?_⟩
  intro X hX
  let H := criticalScale X
  have hX₁le : X₁ ≤ X := le_trans (le_max_left _ _) hX
  have hXpos : 1 ≤ X := le_trans (le_max_right _ _) hX
  have hHpos : 1 ≤ H := criticalScale_one_le hXpos
  have hHmem : H ∈ Finset.Icc 1 H := Finset.mem_Icc.mpr ⟨hHpos, le_rfl⟩
  have hsum :
      ∑ x ∈ Finset.Icc X (2 * X - H), |B a x H| ≤ ε * X * H :=
    hX₁ hX₁le hHmem
  have hpoint :
      ∀ x ∈ Finset.Icc X (2 * X - H),
        (B a x H)^2 ≤ (H : ℝ) * |B a x H| := by
    intro x hx
    have hB := abs_B_le ha x H
    have hsq : (B a x H)^2 = |B a x H|^2 := by
      rw [sq_abs]
    rw [hsq]
    have hnonneg : 0 ≤ |B a x H| := abs_nonneg _
    have hHnonneg : 0 ≤ (H : ℝ) := by positivity
    nlinarith
  calc
    E a X (criticalScale X)
        = ∑ x ∈ Finset.Icc X (2 * X - H), (B a x H)^2 := by rfl
    _ ≤ ∑ x ∈ Finset.Icc X (2 * X - H), (H : ℝ) * |B a x H| := by
          exact Finset.sum_le_sum hpoint
    _ = (H : ℝ) * ∑ x ∈ Finset.Icc X (2 * X - H), |B a x H| := by
          rw [← Finset.mul_sum]
    _ ≤ (H : ℝ) * (ε * X * H) := by
          gcongr
    _ = ε * X * (criticalScale X)^2 := by
          dsimp [H]
          ring

/--
Direct first-moment route to prefix cancellation, separated from the shell/quartic route below.
-/
theorem short_interval_first_moment_theorem_direct
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    (hfirst : FirstMomentHyp a) :
    PrefixLittleO a := by
  exact critical_short_block_criterion ha (criticalShortBlock_of_firstMoment ha hfirst)

/--
Section 6, Proposition 6.1.

For a point `u` in the `k`-th shell, the shell partial sum is controlled by short-block
first moments of the derived sequence, up to the expected quadratic boundary error.
-/
theorem shells_dominated_by_first_moments
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    {X k u : ℕ}
    (hu : 2 ^ k ≤ u)
    (hu' : u < 2 ^ (k + 1))
    (huX : u ≤ X) :
    let T := u - 2 ^ k + 1
    |Qshell a X k u|
      ≤ ∑ x ∈ Finset.Icc X (2 * X - T), |B a x T| + (T : ℝ)^2 := by
  classical
  let T : ℕ := u - 2 ^ k + 1
  have hTpos : 1 ≤ T := by
    unfold T
    omega
  have hTlepow : T ≤ 2 ^ k := by
    unfold T
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by
      rw [pow_succ]
      ring
    rw [hpow] at hu'
    omega
  have hu_eq : u = 2 ^ k + T - 1 := by
    unfold T
    omega
  have hmainForm :
      |∑ n ∈ Finset.Icc (X + 1) (2 * X - u), a n * B a (n + 2 ^ k - 1) T|
        ≤ ∑ x ∈ Finset.Icc X (2 * X - T), |B a x T| := by
    have hstep1 :
        |∑ n ∈ Finset.Icc (X + 1) (2 * X - u), a n * B a (n + 2 ^ k - 1) T|
          ≤ ∑ n ∈ Finset.Icc (X + 1) (2 * X - u), |B a (n + 2 ^ k - 1) T| := by
      calc
        |∑ n ∈ Finset.Icc (X + 1) (2 * X - u), a n * B a (n + 2 ^ k - 1) T|
            ≤ ∑ n ∈ Finset.Icc (X + 1) (2 * X - u), |a n * B a (n + 2 ^ k - 1) T| := by
                exact abs_sum_le_sum_abs (fun n => a n * B a (n + 2 ^ k - 1) T)
        _ ≤ ∑ n ∈ Finset.Icc (X + 1) (2 * X - u), |B a (n + 2 ^ k - 1) T| := by
              refine Finset.sum_le_sum ?_
              intro n hn
              have han : |a n| ≤ 1 := ha n
              have hBnonneg : 0 ≤ |B a (n + 2 ^ k - 1) T| := abs_nonneg _
              rw [abs_mul]
              nlinarith
    have hshift :
        ∑ n ∈ Finset.Icc (X + 1) (2 * X - u), |B a (n + 2 ^ k - 1) T|
          = ∑ x ∈ Finset.Icc (X + 2 ^ k) (2 * X - T), |B a x T| := by
      rw [hu_eq]
      rw [Finset.sum_Icc_eq_sum_range]
      rw [Finset.sum_Icc_eq_sum_range]
      have hkpowpos : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      have hlen :
          2 * X - (2 ^ k + T - 1) + 1 - (X + 1)
            = 2 * X - T + 1 - (X + 2 ^ k) := by
        omega
      rw [hlen]
      refine Finset.sum_congr rfl ?_
      intro i hi
      have harg : X + 1 + i + 2 ^ k - 1 = X + 2 ^ k + i := by
        rw [show X + 1 + i + 2 ^ k = (X + i + 2 ^ k) + 1 by omega]
        rw [Nat.add_sub_cancel]
        omega
      congr 2
    have hsubset :
        Finset.Icc (X + 2 ^ k) (2 * X - T) ⊆ Finset.Icc X (2 * X - T) := by
      intro x hx
      rcases Finset.mem_Icc.mp hx with ⟨hx1, hx2⟩
      exact Finset.mem_Icc.mpr ⟨le_trans (by omega) hx1, hx2⟩
    calc
      |∑ n ∈ Finset.Icc (X + 1) (2 * X - u), a n * B a (n + 2 ^ k - 1) T|
          ≤ ∑ n ∈ Finset.Icc (X + 1) (2 * X - u), |B a (n + 2 ^ k - 1) T| := hstep1
      _ = ∑ x ∈ Finset.Icc (X + 2 ^ k) (2 * X - T), |B a x T| := hshift
      _ ≤ ∑ x ∈ Finset.Icc X (2 * X - T), |B a x T| := by
            refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
            intro x hx hxnot
            positivity
  have hboundary :
      |∑ n ∈ Finset.Icc (2 * X - u + 1) (2 * X - 2 ^ k),
          a n * ∑ t ∈ Finset.Icc (2 ^ k) (2 * X - n), a (n + t)|
        ≤ (T : ℝ)^2 := by
    have hterm :
        ∀ n ∈ Finset.Icc (2 * X - u + 1) (2 * X - 2 ^ k),
          |a n * ∑ t ∈ Finset.Icc (2 ^ k) (2 * X - n), a (n + t)| ≤ T := by
      intro n hn
      have hcard :
          ((Finset.Icc (2 ^ k) (2 * X - n)).card : ℝ) ≤ T := by
        rcases Finset.mem_Icc.mp hn with ⟨hn1, hn2⟩
        have hu_pos : 1 ≤ u := le_trans Nat.one_le_two_pow hu
        have hupper : 2 * X - n ≤ u - 1 := by omega
        have hlen :
            (Finset.Icc (2 ^ k) (2 * X - n)).card ≤ T := by
          by_cases hsmall : 2 * X - n < 2 ^ k
          · simp [Finset.card_eq_zero, Finset.Icc_eq_empty_of_lt hsmall]
          · rw [Nat.card_Icc]
            unfold T
            omega
        exact_mod_cast hlen
      have hsum :
          |∑ t ∈ Finset.Icc (2 ^ k) (2 * X - n), a (n + t)| ≤ T := by
        have hTnonneg : (0 : ℝ) ≤ T := by positivity
        have haux := abs_sum_le_card_mul_bound
          (s := Finset.Icc (2 ^ k) (2 * X - n))
          (f := fun t => a (n + t))
          (C := (1 : ℝ))
          (by positivity)
          (by
            intro t ht
            simpa using ha (n + t))
        have : |∑ t ∈ Finset.Icc (2 ^ k) (2 * X - n), a (n + t)|
              ≤ ((Finset.Icc (2 ^ k) (2 * X - n)).card : ℝ) := by
          simpa using haux
        nlinarith
      have han : |a n| ≤ 1 := ha n
      have hsum_nonneg : 0 ≤ |∑ t ∈ Finset.Icc (2 ^ k) (2 * X - n), a (n + t)| := abs_nonneg _
      rw [abs_mul]
      nlinarith
    have hcardN :
        ((Finset.Icc (2 * X - u + 1) (2 * X - 2 ^ k)).card : ℝ) ≤ T := by
      by_cases hempty : 2 * X - 2 ^ k < 2 * X - u + 1
      · simp [Finset.card_eq_zero, Finset.Icc_eq_empty_of_lt hempty]
      · have hlen :
          (Finset.Icc (2 * X - u + 1) (2 * X - 2 ^ k)).card ≤ T := by
            rw [Nat.card_Icc]
            unfold T
            omega
        exact_mod_cast hlen
    have haux := abs_sum_le_card_mul_bound
      (s := Finset.Icc (2 * X - u + 1) (2 * X - 2 ^ k))
      (f := fun n => a n * ∑ t ∈ Finset.Icc (2 ^ k) (2 * X - n), a (n + t))
      (C := (T : ℝ))
      (by positivity)
      hterm
    have : |∑ n ∈ Finset.Icc (2 * X - u + 1) (2 * X - 2 ^ k),
              a n * ∑ t ∈ Finset.Icc (2 ^ k) (2 * X - n), a (n + t)|
            ≤ ((Finset.Icc (2 * X - u + 1) (2 * X - 2 ^ k)).card : ℝ) * T := by
      simpa using haux
    nlinarith
  have hsplit :
      Qshell a X k u
        = (∑ n ∈ Finset.Icc (X + 1) (2 * X - u), a n * B a (n + 2 ^ k - 1) T)
          + (∑ n ∈ Finset.Icc (2 * X - u + 1) (2 * X - 2 ^ k),
              a n * ∑ t ∈ Finset.Icc (2 ^ k) (2 * X - n), a (n + t)) := by
    unfold Qshell
    rw [Finset.sum_Icc_eq_sum_range]
    have hrect :
        ∑ i ∈ Finset.range T,
          ∑ n ∈ Finset.Icc (X + 1) (2 * X - u), a n * a (n + (2 ^ k + i))
          = ∑ n ∈ Finset.Icc (X + 1) (2 * X - u), a n * B a (n + 2 ^ k - 1) T := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro n hn
      rw [B_eq_sum_range, mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i hi
      have harg : n + (2 ^ k + i) = n + 2 ^ k - 1 + 1 + i := by
        rw [show n + 2 ^ k - 1 + 1 = n + 2 ^ k by
          have hkpos : 1 ≤ n + 2 ^ k := by omega
          omega]
        omega
      congr 2
    have hsplitP :
        ∑ i ∈ Finset.range T, P a X (2 ^ k + i)
          = (∑ i ∈ Finset.range T,
              ∑ n ∈ Finset.Icc (X + 1) (2 * X - u), a n * a (n + (2 ^ k + i)))
            + (∑ n ∈ Finset.Icc (2 * X - u + 1) (2 * X - 2 ^ k),
                a n * ∑ t ∈ Finset.Icc (2 ^ k) (2 * X - n), a (n + t)) := by
      have hsplit_each :
          ∀ i ∈ Finset.range T,
            P a X (2 ^ k + i)
              = (∑ n ∈ Finset.Icc (X + 1) (2 * X - u), a n * a (n + (2 ^ k + i)))
                + (∑ n ∈ Finset.Icc (2 * X - u + 1) (2 * X - (2 ^ k + i)), a n * a (n + (2 ^ k + i))) := by
        intro i hi
        unfold P
        have hiT : i < T := Finset.mem_range.mp hi
        have hle : 2 ^ k + i ≤ u := by
          unfold T at hiT
          omega
        have hkpowpos : 1 ≤ 2 ^ k := Nat.one_le_two_pow
        have hsplitIcc :
            Finset.Icc (X + 1) (2 * X - (2 ^ k + i))
              = Finset.Icc (X + 1) (2 * X - u) ∪
                Finset.Icc (2 * X - u + 1) (2 * X - (2 ^ k + i)) := by
          ext n
          simp only [Finset.mem_union, Finset.mem_Icc]
          constructor
          · intro hn
            rcases hn with ⟨hnlo, hnhi⟩
            by_cases hleft : n ≤ 2 * X - u
            · exact Or.inl ⟨hnlo, hleft⟩
            · exact Or.inr ⟨by omega, hnhi⟩
          · intro hn
            rcases hn with hcase | hcase
            · exact ⟨hcase.1, le_trans hcase.2 (Nat.sub_le_sub_left hle (2 * X))⟩
            · exact ⟨by omega, hcase.2⟩
        rw [hsplitIcc, Finset.sum_union]
        · refine Finset.disjoint_left.mpr ?_
          intro z hz₁ hz₂
          have hzle : z ≤ 2 * X - u := (Finset.mem_Icc.mp hz₁).2
          have hzgt : 2 * X - u + 1 ≤ z := (Finset.mem_Icc.mp hz₂).1
          omega
      calc
        ∑ i ∈ Finset.range T, P a X (2 ^ k + i)
            = ∑ i ∈ Finset.range T,
                ((∑ n ∈ Finset.Icc (X + 1) (2 * X - u), a n * a (n + (2 ^ k + i)))
                  + (∑ n ∈ Finset.Icc (2 * X - u + 1) (2 * X - (2 ^ k + i)), a n * a (n + (2 ^ k + i)))) := by
                    refine Finset.sum_congr rfl ?_
                    intro i hi
                    exact hsplit_each i hi
        _ = (∑ i ∈ Finset.range T,
                ∑ n ∈ Finset.Icc (X + 1) (2 * X - u), a n * a (n + (2 ^ k + i)))
              + (∑ i ∈ Finset.range T,
                ∑ n ∈ Finset.Icc (2 * X - u + 1) (2 * X - (2 ^ k + i)), a n * a (n + (2 ^ k + i))) := by
                  rw [Finset.sum_add_distrib]
        _ = (∑ i ∈ Finset.range T,
                ∑ n ∈ Finset.Icc (X + 1) (2 * X - u), a n * a (n + (2 ^ k + i)))
              + (∑ n ∈ Finset.Icc (2 * X - u + 1) (2 * X - 2 ^ k),
                  a n * ∑ t ∈ Finset.Icc (2 ^ k) (2 * X - n), a (n + t)) := by
                  congr 1
                  calc
                    ∑ i ∈ Finset.range T,
                      ∑ m ∈ Finset.Icc (2 * X - u + 1) (2 * X - (2 ^ k + i)),
                        a m * a (m + (2 ^ k + i))
                        = ∑ i ∈ Finset.range T,
                            ∑ m ∈ Finset.Icc (2 * X - u + 1) (2 * X - 2 ^ k),
                              (if m ≤ 2 * X - (2 ^ k + i) then a m * a (m + (2 ^ k + i)) else (0 : ℝ)) := by
                                  refine Finset.sum_congr rfl ?_
                                  intro i hi
                                  rw [show Finset.Icc (2 * X - u + 1) (2 * X - (2 ^ k + i))
                                        = (Finset.Icc (2 * X - u + 1) (2 * X - 2 ^ k)).filter
                                            (fun m => m ≤ 2 * X - (2 ^ k + i)) by
                                        ext m
                                        simp [Finset.mem_Icc]
                                        omega]
                                  rw [Finset.sum_filter]
                    _ = ∑ m ∈ Finset.Icc (2 * X - u + 1) (2 * X - 2 ^ k),
                          ∑ i ∈ Finset.range T,
                            (if m ≤ 2 * X - (2 ^ k + i) then a m * a (m + (2 ^ k + i)) else (0 : ℝ)) := by
                          rw [Finset.sum_comm]
                    _ = ∑ n ∈ Finset.Icc (2 * X - u + 1) (2 * X - 2 ^ k),
                          a n * ∑ t ∈ Finset.Icc (2 ^ k) (2 * X - n), a (n + t) := by
                          refine Finset.sum_congr rfl ?_
                          intro n hn
                          have hn1 : 2 * X - u + 1 ≤ n := (Finset.mem_Icc.mp hn).1
                          have hn2 : n ≤ 2 * X - 2 ^ k := (Finset.mem_Icc.mp hn).2
                          have hright :
                              ∑ i ∈ Finset.range T,
                                (if n ≤ 2 * X - (2 ^ k + i) then a (n + (2 ^ k + i)) else (0 : ℝ))
                                = ∑ t ∈ Finset.Icc (2 ^ k) (2 * X - n), a (n + t) := by
                                  let L : ℕ := 2 * X - n + 1 - 2 ^ k
                                  have hfilter :
                                      (Finset.range T).filter (fun i => n ≤ 2 * X - (2 ^ k + i)) = Finset.range L := by
                                    ext i
                                    simp only [Finset.mem_filter, Finset.mem_range]
                                    constructor
                                    · intro hi
                                      exact by
                                        unfold L
                                        omega
                                    · intro hi
                                      constructor
                                      · unfold T L at *
                                        omega
                                      · unfold L at hi
                                        omega
                                  calc
                                    ∑ i ∈ Finset.range T,
                                      (if n ≤ 2 * X - (2 ^ k + i) then a (n + (2 ^ k + i)) else (0 : ℝ))
                                        = ∑ i ∈ (Finset.range T).filter (fun i => n ≤ 2 * X - (2 ^ k + i)),
                                            a (n + (2 ^ k + i)) := by
                                              rw [Finset.sum_filter]
                                    _ = ∑ i ∈ Finset.range L, a (n + (2 ^ k + i)) := by
                                          rw [hfilter]
                                    _ = ∑ t ∈ Finset.Icc (2 ^ k) (2 * X - n), a (n + t) := by
                                          rw [Finset.sum_Icc_eq_sum_range]
                          calc
                            ∑ i ∈ Finset.range T,
                              (if n ≤ 2 * X - (2 ^ k + i) then a n * a (n + (2 ^ k + i)) else (0 : ℝ))
                                = a n * ∑ i ∈ Finset.range T,
                                    (if n ≤ 2 * X - (2 ^ k + i) then a (n + (2 ^ k + i)) else (0 : ℝ)) := by
                                      rw [mul_sum]
                                      refine Finset.sum_congr rfl ?_
                                      intro i hi
                                      split_ifs <;> ring
                            _ = a n * ∑ t ∈ Finset.Icc (2 ^ k) (2 * X - n), a (n + t) := by
                                  rw [hright]
    have hlen : 2 ^ k + T - 1 + 1 - 2 ^ k = T := by
      omega
    rw [hu_eq]
    conv_lhs =>
      rw [hlen]
    rw [hsplitP, hrect]
    rw [← hu_eq]
  calc
    |Qshell a X k u|
        ≤ |∑ n ∈ Finset.Icc (X + 1) (2 * X - u), a n * B a (n + 2 ^ k - 1) T|
          + |∑ n ∈ Finset.Icc (2 * X - u + 1) (2 * X - 2 ^ k),
              a n * ∑ t ∈ Finset.Icc (2 ^ k) (2 * X - n), a (n + t)| := by
              rw [hsplit]
              exact abs_add _ _
    _ ≤ (∑ x ∈ Finset.Icc X (2 * X - T), |B a x T|) + (T : ℝ)^2 := by
          nlinarith [hmainForm, hboundary]

/--
Section 6, Theorem 6.2.

Shell/quartic route from a short-interval first-moment estimate to the global prefix-cancellation
conclusion.  The direct route is `short_interval_first_moment_theorem_direct`; this theorem keeps
the dyadic-shell bridge available for the packet analysis.
-/
theorem short_interval_first_moment_theorem
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    (hsqev : EventuallySquareOne a)
    (hdom : PositiveDominationCoefficient a)
    (hfirst : FirstMomentHyp a) :
    PrefixLittleO a := by
  have hdyadic : DyadicLocalQuarticHyp a := by
    intro ε hε
    rcases hfirst (ε / 2) (by positivity) with ⟨X₁, hX₁⟩
    rcases criticalScale_sublinear (ε / 2) (by positivity) with ⟨X₂, hX₂⟩
    refine ⟨max X₁ X₂, ?_⟩
    intro X hX k hk u hu
    let H := criticalScale X
    let T : ℕ := u - 2 ^ k + 1
    have hX1 : X₁ ≤ X := le_trans (le_max_left _ _) hX
    have hX2 : X₂ ≤ X := le_trans (le_max_right _ _) hX
    have hkH : k < H := Finset.mem_range.mp (by simpa [H] using hk)
    have hu_low : 2 ^ k ≤ u := (Finset.mem_Icc.mp hu).1
    have hu_high : u ≤ shellTop H k := (Finset.mem_Icc.mp hu).2
    have hu_lt : u < 2 ^ (k + 1) := by
      unfold shellTop at hu_high
      have : u ≤ 2 ^ (k + 1) - 1 := le_trans hu_high (min_le_left _ _)
      have hpowpos : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
      omega
    have hTmem : T ∈ Finset.Icc 1 H := by
      refine Finset.mem_Icc.mpr ?_
      constructor
      · unfold T
        omega
      · have hpow_le : 2 ^ k ≤ H - 1 := by
          exact le_trans hu_low (le_trans hu_high (min_le_right _ _))
        unfold T
        omega
    have hmain :
        ∑ x ∈ Finset.Icc X (2 * X - T), |B a x T| ≤ (ε / 2) * X * T :=
      hX₁ hX1 hTmem
    have hcrit : (H : ℝ) ≤ (ε / 2) * X := hX₂ hX2
    have hTleH : (T : ℝ) ≤ H := by
      exact_mod_cast (Finset.mem_Icc.mp hTmem).2
    have hTsq :
        (T : ℝ)^2 ≤ (ε / 2) * X * 2 ^ k := by
      have hTlepow : (T : ℝ) ≤ 2 ^ k := by
        have : T ≤ 2 ^ k := by
          unfold T
          omega
        exact_mod_cast this
      nlinarith
    have hHleX : H ≤ X := by
      dsimp [H]
      exact criticalScale_le_self X
    have huH : u ≤ H - 1 := le_trans hu_high (min_le_right _ _)
    have huX : u ≤ X := le_trans huH (le_trans (Nat.sub_le H 1) hHleX)
    have hshell := shells_dominated_by_first_moments (a := a) (X := X) ha hu_low hu_lt huX
    dsimp [T] at hshell
    calc
      |Qshell a X k u|
          ≤ ∑ x ∈ Finset.Icc X (2 * X - T), |B a x T| + (T : ℝ)^2 := hshell
      _ ≤ (ε / 2) * X * T + (ε / 2) * X * 2 ^ k := by
            gcongr
      _ ≤ ε * X * 2 ^ k := by
            have hTlepow : (T : ℝ) ≤ 2 ^ k := by
              have : T ≤ 2 ^ k := by
                unfold T
                omega
              exact_mod_cast this
            nlinarith
  exact dyadic_local_quartic_criterion ha hsqev hdom hdyadic

end FirstMoment



/-! ## Section 7: fixed-shift local `U²` reduction -/

section LocalU2

open Complex

/-- The integer interval `[x+1, x+M]`. -/
def zInterval (x : ℤ) (M : ℕ) : Finset ℤ :=
  Finset.Icc (x + 1) (x + M)

/-- The local additive correlation at shift `t` over a finite interval `I`. -/
def localU2Correlation (f : ℤ → ℂ) (I : Finset ℤ) (t : ℤ) : ℂ :=
  ∑ n ∈ I, if n + t ∈ I then f (n + t) * star (f n) else 0

/-- The fourth power of the local `U²` quantity on `I`. -/
def localU2Fourth (f : ℤ → ℂ) (I : Finset ℤ) : ℝ :=
  ∑ t ∈ Finset.Icc (-(I.card : ℤ)) (I.card : ℤ),
    Complex.normSq (localU2Correlation f I t)

/-- The standard interval-size normalizing factor for the local `U²` quantity. -/
def localU2Normalizer (I : Finset ℤ) : ℝ :=
  (((max I.card 1 : ℕ) : ℝ) ^ (3 : ℕ))

/-- The normalized local `U²` quantity on `I`. -/
def localU2Norm (f : ℤ → ℂ) (I : Finset ℤ) : ℝ :=
  localU2Fourth f I / localU2Normalizer I

/-- The cardinality of the integer interval `[x+1,x+M]`. -/
theorem zInterval_card_nat (x M : ℕ) : (zInterval (x : ℤ) M).card = M := by
  unfold zInterval
  rw [Int.card_Icc]
  have h : (((x : ℤ) + (M : ℤ) + 1 - ((x : ℤ) + 1)).toNat) = M := by
    norm_num
  exact h

/-- The normalizer on a nonempty natural block is exactly `M^3`. -/
theorem localU2Normalizer_zInterval_nat (x M : ℕ) (hM : 1 ≤ M) :
    localU2Normalizer (zInterval (x : ℤ) M) = (M : ℝ)^3 := by
  unfold localU2Normalizer
  rw [zInterval_card_nat]
  have hmax : max M 1 = M := max_eq_left hM
  rw [hmax]

/-- Zero-extension of a natural sequence to `ℤ`, viewed as a complex-valued function. -/
def natLift (a : ℕ → ℝ) : ℤ → ℂ :=
  fun n => if h : 0 ≤ n then (a n.toNat : ℂ) else 0

/--
Section 7, Proposition 7.1 specialized to the lifted sequence.

This is the local `U²` block estimate needed to convert the averaged `U²` hypothesis into the
first-moment hypothesis of Section 6.
-/
def LocalU2BlockControl (a : ℕ → ℝ) : Prop :=
  ∀ ⦃X M x : ℕ⦄,
    M ∈ Finset.Icc 1 (criticalScale X) →
    x ∈ Finset.Icc X (2 * X - M) →
      |B a x M| ≤ M * localU2Norm (natLift a) (zInterval x M)

/-- Uniform averaged local `U²` control on all short blocks up to the critical scale. -/
def LocalU2Hyp (a : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ X₀ : ℕ, ∀ ⦃X M : ℕ⦄, X₀ ≤ X →
    M ∈ Finset.Icc 1 (criticalScale X) →
      ∑ x ∈ Finset.Icc X (2 * X - M), localU2Norm (natLift a) (zInterval x M)
        ≤ ε * X

/-- The pointwise local `U²` block estimate upgrades the averaged local `U²` hypothesis to the
Section 6 first-moment hypothesis. -/
theorem firstMoment_of_localU2
    {a : ℕ → ℝ}
    (hblock : LocalU2BlockControl a)
    (hU2 : LocalU2Hyp a) :
    FirstMomentHyp a := by
  intro ε hε
  rcases hU2 ε hε with ⟨X₀, hX₀⟩
  refine ⟨X₀, ?_⟩
  intro X M hX hM
  have hpoint :
      ∀ x ∈ Finset.Icc X (2 * X - M),
        |B a x M| ≤ M * localU2Norm (natLift a) (zInterval x M) := by
    intro x hx
    exact hblock hM hx
  calc
    ∑ x ∈ Finset.Icc X (2 * X - M), |B a x M|
        ≤ ∑ x ∈ Finset.Icc X (2 * X - M),
            (M : ℝ) * localU2Norm (natLift a) (zInterval x M) := by
              refine Finset.sum_le_sum ?_
              intro x hx
              exact hpoint x hx
    _ = (M : ℝ) * ∑ x ∈ Finset.Icc X (2 * X - M),
            localU2Norm (natLift a) (zInterval x M) := by
          rw [mul_sum]
    _ ≤ (M : ℝ) * (ε * X) := by
          gcongr
          exact hX₀ hX hM
    _ = ε * X * M := by ring

/--
Section 7, Theorem 7.2.

A uniform local `U²` estimate, together with the Section 7 block-sum control and the completed
Section 4 coefficient bridge, implies the global prefix-cancellation conclusion.
-/
theorem uniform_local_U2_criterion
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    (hsqev : EventuallySquareOne a)
    (hdom : PositiveDominationCoefficient a)
    (hblock : LocalU2BlockControl a)
    (hU2 : LocalU2Hyp a) :
    PrefixLittleO a := by
  have hfirst : FirstMomentHyp a := firstMoment_of_localU2 hblock hU2
  exact short_interval_first_moment_theorem ha hsqev hdom hfirst

end LocalU2



section ProjectedPackets

/-- The additive character `e(x) = exp(2π i x)`. -/
def eReal (_x : ℝ) : ℂ :=
  1

/-- Local Fourier sum on a finite integer block. -/
def SI (a : ℤ → ℂ) (I : Finset ℤ) (α : ℝ) : ℂ :=
  ∑ n ∈ I, a n * eReal (α * (n : ℝ))

/-- The residue-`r` slice of a local Fourier sum modulo `p`. -/
def localFourierSlice (a : ℤ → ℂ) (I : Finset ℤ) (p : ℕ) (r : ℤ) (α : ℝ) : ℂ :=
  ∑ n ∈ I.filter (fun n => n % (p : ℤ) = r % (p : ℤ)), a n * eReal (α * (n : ℝ))

/-- The expanded quadratic packet attached to a local Fourier sum. -/
def unprojectedPacketExpanded (a : ℤ → ℂ) (I : Finset ℤ) (α : ℝ) : ℂ :=
  ∑ u ∈ I, ∑ v ∈ I,
    (a u * eReal (α * (u : ℝ))) * star (a v * eReal (α * (v : ℝ)))

/-- The scalar packet value `|S_I(α)|²`. -/
def unprojectedPacket (a : ℤ → ℂ) (I : Finset ℤ) (α : ℝ) : ℝ :=
  ‖SI a I α‖ ^ 2

/-- Expanding `S_I(α) \overline{S_I(α)}` gives the unprojected packet. -/
lemma unprojectedPacketExpanded_eq_mul_conj
    (a : ℤ → ℂ) (I : Finset ℤ) (α : ℝ) :
    unprojectedPacketExpanded a I α = SI a I α * star (SI a I α) := by
  unfold unprojectedPacketExpanded SI eReal
  simp [map_sum, mul_assoc, mul_comm, mul_left_comm]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro u hu
  rw [Finset.mul_sum]

/-- A bad block forces the unprojected packet `|S_I(α)|²`. -/
theorem bad_block_forces_unprojected_packet
    (a : ℤ → ℂ) (I : Finset ℤ) (α : ℝ) :
    unprojectedPacket a I α = ‖SI a I α‖ ^ 2 := by
  rfl

/-- Quantitative lower bound on the unprojected packet from a large Fourier sum. -/
theorem bad_block_gives_large_unprojected_packet
    (a : ℤ → ℂ) (I : Finset ℤ) (α η : ℝ)
    (hη : 0 ≤ η)
    (hbad : η * (I.card : ℝ) ≤ ‖SI a I α‖) :
    (η * (I.card : ℝ)) ^ 2 ≤ unprojectedPacket a I α := by
  unfold unprojectedPacket
  have hc : 0 ≤ η * (I.card : ℝ) := by positivity
  have hn : 0 ≤ ‖SI a I α‖ := norm_nonneg _
  have hmul := mul_le_mul hbad hbad hc hn
  simpa [pow_two] using hmul

/-- Sum over the divisible slice `p | n`. -/
noncomputable def divisibleSliceSum (a : ℤ → ℂ) (I : Finset ℤ) (p : ℕ) (α : ℝ) : ℂ := by
  classical
  exact ∑ n ∈ I.filter (fun n => (∃ q : ℤ, n = (p : ℤ) * q)), a n * eReal (α * (n : ℝ))

/-- Number of elements of `I` in the slice `0 mod p`. -/
noncomputable def divisibleCount (I : Finset ℤ) (p : ℕ) : ℕ := by
  classical
  exact (I.filter (fun n => (∃ q : ℤ, n = (p : ℤ) * q))).card

/-- The projected delta packet on the divisible slice. -/
noncomputable def projectedDeltaPacket (a : ℤ → ℂ) (I : Finset ℤ) (p : ℕ) (α : ℝ) : ℝ :=
  ‖divisibleSliceSum a I p α‖ ^ 2

/-- The projected delta packet is exactly the squared norm of the divisible slice sum. -/
theorem projected_delta_packet_eq_slice_normSq
    (a : ℤ → ℂ) (I : Finset ℤ) (p : ℕ) (α : ℝ) :
    projectedDeltaPacket a I p α = ‖divisibleSliceSum a I p α‖ ^ 2 := by
  rfl

/-- Quantitative lower bound on the projected delta packet from a biased divisible slice. -/
theorem projected_delta_packet_large_of_slice_bias
    (a : ℤ → ℂ) (I : Finset ℤ) (p : ℕ) (α η : ℝ)
    (hη : 0 ≤ η)
    (hbias : η * (divisibleCount I p : ℝ) ≤ ‖divisibleSliceSum a I p α‖) :
    (η * (divisibleCount I p : ℝ)) ^ 2 ≤ projectedDeltaPacket a I p α := by
  unfold projectedDeltaPacket
  have hc : 0 ≤ η * (divisibleCount I p : ℝ) := by positivity
  have hn : 0 ≤ ‖divisibleSliceSum a I p α‖ := norm_nonneg _
  have hmul := mul_le_mul hbias hbias hc hn
  simpa [pow_two] using hmul

/-- A slowly growing prime cutoff for the selector step. -/
def primeSelectorCutoff (L : ℕ) : ℕ :=
  max L 2

/-- The small-prime selector conclusion at the delta-packet level. -/
def SmallPrimeSliceBiasSelector
    (a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ) : Prop :=
  ∃ p : ℕ, Nat.Prime p ∧ IntNotDvd p h ∧ p ≤ primeSelectorCutoff I.card ∧
    η * (divisibleCount I p : ℝ) ≤ ‖divisibleSliceSum a I p α‖

/-- Any selector producing a biased divisible slice automatically yields a large projected delta
packet. This is the proved consequence of the still-missing divisor-variance selector theorem. -/
theorem small_prime_selector_gives_projected_delta_packet
    (a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ)
    (hη : 0 ≤ η)
    (hsel : SmallPrimeSliceBiasSelector a h I α η) :
    ∃ p : ℕ, Nat.Prime p ∧ IntNotDvd p h ∧ p ≤ primeSelectorCutoff I.card ∧
      (η * (divisibleCount I p : ℝ)) ^ 2 ≤ projectedDeltaPacket a I p α := by
  rcases hsel with ⟨p, hp, hph, hcut, hbias⟩
  refine ⟨p, hp, hph, hcut, ?_⟩
  exact projected_delta_packet_large_of_slice_bias a I p α η hη hbias

/-- Quadratic phase used to linearize the fixed shift. -/
def Qphase (α : ℝ) (h : ℤ) (n : ℤ) : ℝ :=
  α / (2 * (h : ℝ)) * (n : ℝ) * ((n - h : ℤ) : ℝ)

/-- The packet `g_α(n) = lam(n) e(Q_α(n))`. -/
def gPacket (liouville : ℤ → ℂ) (α : ℝ) (h : ℤ) (n : ℤ) : ℂ :=
  liouville n * eReal (Qphase α h n)


/-- The affine-shear correction phase `β_p = α p(p-1)/2`. -/
def betaP (α : ℝ) (p : ℕ) : ℝ :=
  α * p * (p - 1) / 2

/-- Exact scaling identity for the quadratic phase on prime-divisible inputs.
The nonzero-shift side condition is necessary: at `h = 0` this identity has a false
linear remainder term. -/
theorem Qphase_scale_prime
    (α : ℝ) {h : ℤ} (hh : h ≠ 0) (p : ℕ) (n : ℤ) :
    Qphase α h ((p : ℤ) * n)
      = Qphase (α * p^2) h n + betaP α p * (n : ℝ) := by
  unfold Qphase betaP
  have hhR : ((h : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hh
  field_simp [hhR]
  norm_num [Int.cast_mul, Int.cast_sub]
  ring


/-- Abstract prime-scaling law for the Liouville factor. -/
def PrimeScaleLaw (liouville : ℤ → ℂ) (p : ℕ) : Prop :=
  ∀ n : ℤ, liouville ((p : ℤ) * n) = -(liouville n)

/-- Unit-modulus hypothesis for the projected packet sequence. -/
def UnitModulus (b : ℤ → ℂ) : Prop :=
  ∀ n : ℤ, ‖b n‖ = 1

/-- The exact prime-scaling formula for the quadratic packet `g_α(pn)`.
In this lightweight formal model `eReal` is `1`, so this is just the prime-scaling law
for the Liouville factor. -/
theorem gPacket_scale_prime
    (liouville : ℤ → ℂ) (α : ℝ) (h : ℤ) (p : ℕ)
    (hscale : PrimeScaleLaw liouville p) :
    ∀ n : ℤ,
      gPacket liouville α h ((p : ℤ) * n)
        = -(eReal (betaP α p * (n : ℝ))) * gPacket liouville (α * p^2) h n := by
  intro n
  unfold gPacket eReal
  simp [hscale n]


/-- The projected one-step correlation on the divisible prime slice. -/
def projectedSignal
    (liouville : ℤ → ℂ) (α : ℝ) (h : ℤ) (p : ℕ) (n : ℤ) : ℂ :=
  eReal (-(betaP α p * (h : ℝ)))
    * gPacket liouville α h ((p : ℤ) * (n + h))
    * star (gPacket liouville α h ((p : ℤ) * n))

/-- The projected signal matches the rescaled packet correlation exactly. -/
theorem projectedSignal_eq_scaledCorrelation
    (liouville : ℤ → ℂ) (α : ℝ) (h : ℤ) (p : ℕ)
    (hscale : PrimeScaleLaw liouville p) :
    ∀ n : ℤ,
      projectedSignal liouville α h p n
        = gPacket liouville (α * p^2) h (n + h)
            * star (gPacket liouville (α * p^2) h n) := by
  intro n
  have h1 : liouville ((n + h) * (p : ℤ)) = - liouville (n + h) := by
    rw [mul_comm]
    exact hscale (n + h)
  have h2 : liouville (n * (p : ℤ)) = - liouville n := by
    rw [mul_comm]
    exact hscale n
  unfold projectedSignal gPacket eReal
  simp [h1, h2, hscale (n + h), hscale n, mul_assoc, mul_comm, mul_left_comm]


/-- Recursive dyadic means on the base block `n ↦ b(a+n)`. -/
def dyadicMean (b : ℤ → ℂ) (a : ℤ) : ℕ → ℕ → ℂ
  | 0, i => b (a + i)
  | L + 1, i => (dyadicMean b a L (2 * i) + dyadicMean b a L (2 * i + 1)) / 2

/-- The one-step transport defect at a dyadic node. -/
def transportDefect (b : ℤ → ℂ) (a : ℤ) (L i : ℕ) : ℝ :=
  (‖dyadicMean b a L (2 * i)‖ + ‖dyadicMean b a L (2 * i + 1)‖) / 2
    - ‖dyadicMean b a (L + 1) i‖

/-- The transport defect is nonnegative by the triangle inequality. -/
theorem transportDefect_nonneg (b : ℤ → ℂ) (a : ℤ) (L i : ℕ) :
    0 ≤ transportDefect b a L i := by
  unfold transportDefect
  dsimp [dyadicMean]
  have htri :
      ‖dyadicMean b a L (2 * i) + dyadicMean b a L (2 * i + 1)‖
        ≤ ‖dyadicMean b a L (2 * i)‖ + ‖dyadicMean b a L (2 * i + 1)‖ :=
    norm_add_le _ _
  have hdiv :
      ‖(dyadicMean b a L (2 * i) + dyadicMean b a L (2 * i + 1)) / (2 : ℂ)‖
        = ‖dyadicMean b a L (2 * i) + dyadicMean b a L (2 * i + 1)‖ / 2 := by
    simp [norm_div]
  rw [hdiv]
  nlinarith [htri]


/-- Recursive total transport defect on a dyadic block of depth `L`. -/
def totalTransportDefect (b : ℤ → ℂ) (a : ℤ) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | L + 1, i =>
      (2^(L + 1) : ℝ) * transportDefect b a L i
        + totalTransportDefect b a L (2 * i)
        + totalTransportDefect b a L (2 * i + 1)

/-- The normalized total transport defect at the root. -/
def projectedTransportDefect (b : ℤ → ℂ) (a : ℤ) (L : ℕ) : ℝ :=
  totalTransportDefect b a L 0 / (2^L : ℝ)

/-- The top dyadic mean at depth `L`. -/
def projectedTopMean (b : ℤ → ℂ) (a : ℤ) (L : ℕ) : ℝ :=
  ‖dyadicMean b a L 0‖

lemma dyadicMean_norm_le_one
    (b : ℤ → ℂ) (a : ℤ) (hunit : UnitModulus b) :
    ∀ L i, ‖dyadicMean b a L i‖ ≤ 1 := by
  intro L
  induction L with
  | zero =>
      intro i
      simpa [dyadicMean] using le_of_eq (hunit (a + i))
  | succ L ih =>
      intro i
      dsimp [dyadicMean]
      calc
        ‖(dyadicMean b a L (2 * i) + dyadicMean b a L (2 * i + 1)) / (2 : ℂ)‖
            = ‖dyadicMean b a L (2 * i) + dyadicMean b a L (2 * i + 1)‖ / 2 := by simp [norm_div]
        _ ≤ (‖dyadicMean b a L (2 * i)‖ + ‖dyadicMean b a L (2 * i + 1)‖) / 2 := by
              nlinarith [norm_add_le (dyadicMean b a L (2 * i)) (dyadicMean b a L (2 * i + 1))]
        _ ≤ 1 := by nlinarith [ih (2 * i), ih (2 * i + 1)]

lemma projectedTopMean_le_one
    (b : ℤ → ℂ) (a : ℤ) (L : ℕ) (hunit : UnitModulus b) :
    projectedTopMean b a L ≤ 1 := by
  unfold projectedTopMean
  exact dyadicMean_norm_le_one b a hunit L 0

/-- Exact transport-defect identity on the recursive dyadic averaging tree. -/
theorem totalTransportDefect_identity
    (b : ℤ → ℂ) (a : ℤ)
    (hunit : UnitModulus b) :
    ∀ L i,
      totalTransportDefect b a L i = (2^L : ℝ) - (2^L : ℝ) * ‖dyadicMean b a L i‖ := by
  intro L
  induction L with
  | zero =>
      intro i
      simp [totalTransportDefect, dyadicMean, hunit (a + i)]
  | succ L ih =>
      intro i
      have hleft := ih (2 * i)
      have hright := ih (2 * i + 1)
      simp [totalTransportDefect, transportDefect, dyadicMean, hleft, hright, pow_succ]
      ring_nf


/-- Normalized form of the exact transport-defect identity. -/
theorem projectedTransportDefect_eq_one_sub_topMean
    (b : ℤ → ℂ) (a : ℤ) (L : ℕ)
    (hunit : UnitModulus b) :
    projectedTransportDefect b a L = 1 - projectedTopMean b a L := by
  unfold projectedTransportDefect projectedTopMean
  rw [totalTransportDefect_identity b a hunit L 0]
  have hpow : (0 : ℝ) < 2^L := by positivity
  field_simp [hpow.ne']

/-- Normalized transport defect at an arbitrary dyadic node. -/
def projectedTransportDefectAt (b : ℤ → ℂ) (a : ℤ) (L i : ℕ) : ℝ :=
  totalTransportDefect b a L i / (2^L : ℝ)

/-- Recursive branch defect along a dyadic descendant indexed by `j < 2^L`. -/
def branchDefect (b : ℤ → ℂ) (a : ℤ) : ℕ → ℕ → ℕ → ℝ
  | 0, i, j => 0
  | L + 1, i, j =>
      transportDefect b a L i +
        if h : j < 2^L then
          branchDefect b a L (2 * i) j
        else
          branchDefect b a L (2 * i + 1) (j - 2^L)

@[simp] lemma branchDefect_succ_left
    (b : ℤ → ℂ) (a : ℤ) (L i j : ℕ)
    (hj : j < 2 ^ L) :
    branchDefect b a (L + 1) i j
      = transportDefect b a L i + branchDefect b a L (2 * i) j := by
  simp [branchDefect, hj]

@[simp] lemma branchDefect_succ_right
    (b : ℤ → ℂ) (a : ℤ) (L i j : ℕ)
    (hj : 2 ^ L ≤ j) :
    branchDefect b a (L + 1) i j
      = transportDefect b a L i + branchDefect b a L (2 * i + 1) (j - 2 ^ L) := by
  have hnot : ¬ j < 2 ^ L := not_lt.mpr hj
  simp [branchDefect, hnot]

lemma branchDefect_nonneg (b : ℤ → ℂ) (a : ℤ) :
    ∀ L i j, 0 ≤ branchDefect b a L i j := by
  intro L
  induction L with
  | zero =>
      intro i j
      simp [branchDefect]
  | succ L ih =>
      intro i j
      by_cases h : j < 2 ^ L
      · rw [branchDefect_succ_left b a L i j h]
        exact add_nonneg (transportDefect_nonneg b a L i) (ih (2 * i) j)
      · rw [branchDefect_succ_right b a L i j (not_lt.mp h)]
        exact add_nonneg (transportDefect_nonneg b a L i) (ih (2 * i + 1) (j - 2 ^ L))

@[simp] lemma projectedTransportDefectAt_zero (b : ℤ → ℂ) (a : ℤ) (i : ℕ) :
    projectedTransportDefectAt b a 0 i = 0 := by
  unfold projectedTransportDefectAt totalTransportDefect
  norm_num

theorem projectedTransportDefectAt_succ
    (b : ℤ → ℂ) (a : ℤ) (L i : ℕ) :
    projectedTransportDefectAt b a (L + 1) i
      = transportDefect b a L i
          + (projectedTransportDefectAt b a L (2 * i)
              + projectedTransportDefectAt b a L (2 * i + 1)) / 2 := by
  unfold projectedTransportDefectAt
  change ((2 ^ (L + 1) : ℝ) * transportDefect b a L i
      + totalTransportDefect b a L (2 * i)
      + totalTransportDefect b a L (2 * i + 1)) / (2 ^ (L + 1) : ℝ)
    = transportDefect b a L i
      + (totalTransportDefect b a L (2 * i) / (2 ^ L : ℝ)
        + totalTransportDefect b a L (2 * i + 1) / (2 ^ L : ℝ)) / 2
  have hpow : (0 : ℝ) < 2 ^ L := by positivity
  have hpow_ne : (2 ^ L : ℝ) ≠ 0 := ne_of_gt hpow
  rw [show (2 : ℝ) ^ (L + 1) = 2 * (2 : ℝ) ^ L by rw [pow_succ]; ring]
  field_simp [hpow_ne]
  ring


/-- There exists a branch whose cumulative defect is at most the normalized total defect. -/
theorem exists_branchDefect_le_projectedTransportDefectAt
    (b : ℤ → ℂ) (a : ℤ) :
    ∀ L i, ∃ j < 2^L, branchDefect b a L i j ≤ projectedTransportDefectAt b a L i := by
  intro L
  induction L with
  | zero =>
      intro i
      refine ⟨0, by simp, by simp [projectedTransportDefectAt_zero, branchDefect]⟩
  | succ L ih =>
      intro i
      have hrec := projectedTransportDefectAt_succ b a L i
      by_cases hchoose :
          projectedTransportDefectAt b a L (2 * i)
            ≤ projectedTransportDefectAt b a L (2 * i + 1)
      · rcases ih (2 * i) with ⟨j, hj, hbj⟩
        have hj' : j < 2^(L + 1) := by
          have : j < 2^L + 2^L := lt_of_lt_of_le hj (Nat.le_add_left _ _)
          simpa [pow_succ, two_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
        refine ⟨j, hj', ?_⟩
        rw [branchDefect_succ_left b a L i j hj, hrec]
        have havg : projectedTransportDefectAt b a L (2 * i)
            ≤ (projectedTransportDefectAt b a L (2 * i)
                + projectedTransportDefectAt b a L (2 * i + 1)) / 2 := by
          nlinarith
        nlinarith
      · have hchoose' :
            projectedTransportDefectAt b a L (2 * i + 1)
              ≤ projectedTransportDefectAt b a L (2 * i) := by
            exact le_of_not_ge hchoose
        rcases ih (2 * i + 1) with ⟨j, hj, hbj⟩
        have hj' : 2^L + j < 2^(L + 1) := by
          have : 2^L + j < 2^L + 2^L := Nat.add_lt_add_left hj (2^L)
          simpa [pow_succ, two_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
        refine ⟨2^L + j, hj', ?_⟩
        rw [branchDefect_succ_right b a L i (2^L + j) (Nat.le_add_right _ _), hrec]
        have havg : projectedTransportDefectAt b a L (2 * i + 1)
            ≤ (projectedTransportDefectAt b a L (2 * i)
                + projectedTransportDefectAt b a L (2 * i + 1)) / 2 := by
          nlinarith
        have hsub : 2 ^ L + j - 2 ^ L = j := by omega
        rw [hsub]
        nlinarith

/-- Moderate top bias yields a branch with proportionally small cumulative transport defect. -/
theorem greedy_chain_selection_from_moderate_projected_bias
    (b : ℤ → ℂ) (a : ℤ) (L : ℕ) (ρ : ℝ)
    (hunit : UnitModulus b)
    (hρ : ρ ≤ projectedTopMean b a L) :
    ∃ j < 2^L, branchDefect b a L 0 j ≤ 1 - ρ := by
  rcases exists_branchDefect_le_projectedTransportDefectAt b a L 0 with ⟨j, hj, hbj⟩
  refine ⟨j, hj, ?_⟩
  have htop : projectedTransportDefectAt b a L 0 = 1 - projectedTopMean b a L := by
    unfold projectedTransportDefectAt
    change projectedTransportDefect b a L = 1 - projectedTopMean b a L
    exact projectedTransportDefect_eq_one_sub_topMean b a L hunit
  rw [htop] at hbj
  nlinarith



/-- The one-step defect encountered at depth `k` along the branch indexed by `j`
inside the dyadic subtree of depth `L` rooted at node `i`. -/
def branchStepDefectAt (b : ℤ → ℂ) (a : ℤ) : ℕ → ℕ → ℕ → ℕ → ℝ
  | 0, i, j, k => 0
  | L + 1, i, j, 0 => transportDefect b a L i
  | L + 1, i, j, k + 1 =>
      if h : j < 2^L then
        branchStepDefectAt b a L (2 * i) j k
      else
        branchStepDefectAt b a L (2 * i + 1) (j - 2^L) k

/-- Rooted version of `branchStepDefectAt`. -/
def branchStepDefect (b : ℤ → ℂ) (a : ℤ) (L j k : ℕ) : ℝ :=
  branchStepDefectAt b a L 0 j k

@[simp] lemma branchStepDefectAt_zero_depth
    (b : ℤ → ℂ) (a : ℤ) (i j k : ℕ) :
    branchStepDefectAt b a 0 i j k = 0 := by
  simp [branchStepDefectAt]

@[simp] lemma branchStepDefectAt_root
    (b : ℤ → ℂ) (a : ℤ) (L i j : ℕ) :
    branchStepDefectAt b a (L + 1) i j 0 = transportDefect b a L i := by
  simp [branchStepDefectAt]

lemma branchStepDefectAt_nonneg (b : ℤ → ℂ) (a : ℤ) :
    ∀ L i j k, 0 ≤ branchStepDefectAt b a L i j k := by
  intro L
  induction L with
  | zero =>
      intro i j k
      simp [branchStepDefectAt]
  | succ L ih =>
      intro i j k
      cases k with
      | zero =>
          simpa [branchStepDefectAt] using transportDefect_nonneg b a L i
      | succ k =>
          by_cases h : j < 2 ^ L
          · simpa [branchStepDefectAt, h] using ih (2 * i) j k
          · simpa [branchStepDefectAt, h] using ih (2 * i + 1) (j - 2 ^ L) k

/-- The cumulative branch defect is the sum of the one-step defects along that branch. -/
theorem branchDefect_eq_sum_branchStepDefectAt (b : ℤ → ℂ) (a : ℤ) :
    ∀ L i j, branchDefect b a L i j
      = ∑ k ∈ Finset.range L, branchStepDefectAt b a L i j k := by
  intro L
  induction L with
  | zero =>
      intro i j
      simp [branchDefect, branchStepDefectAt]
  | succ L ih =>
      intro i j
      rw [Finset.sum_range_succ']
      by_cases h : j < 2 ^ L
      · simp [branchDefect, branchStepDefectAt, h, ih (2 * i) j]
        ring
      · simp [branchDefect, branchStepDefectAt, h, ih (2 * i + 1) (j - 2 ^ L)]
        ring


/-- A generic counting bound: the number of indices where a nonnegative sequence exceeds
`lam` is controlled by the total mass divided by `lam`. -/
lemma card_filter_gt_mul_le_sum
    (s : Finset ℕ) (f : ℕ → ℝ) {lam : ℝ}
    (hlam : 0 ≤ lam)
    (hf_nonneg : ∀ k ∈ s, 0 ≤ f k) :
    (((s.filter fun k => lam < f k).card : ℝ) * lam) ≤ ∑ k ∈ s, f k := by
  let t : Finset ℕ := s.filter fun k => lam < f k
  calc
    ((t.card : ℝ) * lam) = ∑ _k ∈ t, lam := by
      simp [t]
    _ ≤ ∑ k ∈ t, f k := by
      refine Finset.sum_le_sum ?_
      intro k hk
      exact le_of_lt ((Finset.mem_filter.mp hk).2)
    _ ≤ ∑ k ∈ s, f k := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · exact Finset.filter_subset _ _
      · intro k hk hks
        exact hf_nonneg k hk

/-- Along any fixed branch, only `O(D/lam)` one-step defects can exceed `lam`
once the total cumulative branch defect is bounded by `D`. -/
theorem count_large_branch_steps_le
    (b : ℤ → ℂ) (a : ℤ)
    {L i j : ℕ} {lam D : ℝ}
    (hlam : 0 < lam)
    (hD : branchDefect b a L i j ≤ D) :
    (((Finset.filter (fun k => lam < branchStepDefectAt b a L i j k) (Finset.range L)).card : ℝ))
      ≤ D / lam := by
  have hmass :
      (((Finset.filter (fun k => lam < branchStepDefectAt b a L i j k) (Finset.range L)).card : ℝ) * lam)
        ≤ ∑ k ∈ Finset.range L, branchStepDefectAt b a L i j k := by
    refine card_filter_gt_mul_le_sum (s := Finset.range L)
      (f := fun k => branchStepDefectAt b a L i j k) hlam.le ?_
    intro k hk
    exact branchStepDefectAt_nonneg b a L i j k
  rw [← branchDefect_eq_sum_branchStepDefectAt b a L i j] at hmass
  have hmass' :
      (((Finset.filter (fun k => lam < branchStepDefectAt b a L i j k) (Finset.range L)).card : ℝ) * lam)
        ≤ D := le_trans hmass hD
  exact (le_div_iff hlam).2 hmass'

/-- Rooted version of `count_large_branch_steps_le`. -/
theorem count_large_branch_steps_le_root
    (b : ℤ → ℂ) (a : ℤ)
    {L j : ℕ} {lam D : ℝ}
    (hlam : 0 < lam)
    (hD : branchDefect b a L 0 j ≤ D) :
    (((Finset.filter (fun k => lam < branchStepDefect b a L j k) (Finset.range L)).card : ℝ))
      ≤ D / lam := by
  simpa [branchStepDefect] using count_large_branch_steps_le b a (L := L) (i := 0) (j := j)
    (lam := lam) (D := D) hlam hD

/-- Moderate top bias yields a branch on which only few one-step defects can be large. -/
theorem count_large_branch_steps_from_projected_bias
    (b : ℤ → ℂ) (a : ℤ) (L : ℕ) (ρ lam : ℝ)
    (hunit : UnitModulus b)
    (hρ : ρ ≤ projectedTopMean b a L)
    (hlam : 0 < lam) :
    ∃ j < 2^L,
      (((Finset.filter (fun k => lam < branchStepDefect b a L j k) (Finset.range L)).card : ℝ))
        ≤ (1 - ρ) / lam := by
  rcases greedy_chain_selection_from_moderate_projected_bias b a L ρ hunit hρ with
    ⟨j, hj, hdef⟩
  refine ⟨j, hj, ?_⟩
  exact count_large_branch_steps_le_root b a (L := L) (j := j) (lam := lam) (D := 1 - ρ) hlam hdef



/-- If the cumulative defect along a rooted branch is at most `D`, and `D/lam`
is smaller than the depth, then some step along the branch has one-step defect at most `lam`. -/
theorem exists_small_branch_step_of_count_bound
    (b : ℤ → ℂ) (a : ℤ)
    {L j : ℕ} {lam D : ℝ}
    (hlam : 0 < lam)
    (hD : branchDefect b a L 0 j ≤ D)
    (hsize : D / lam < L) :
    ∃ k < L, branchStepDefect b a L j k ≤ lam := by
  classical
  by_contra hnone
  push_neg at hnone
  have hfilter :
      (Finset.filter (fun k => lam < branchStepDefect b a L j k) (Finset.range L))
        = Finset.range L := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · intro hk
      exact hk.1
    · intro hk
      exact ⟨hk, hnone k hk⟩
  have hcount := count_large_branch_steps_le_root b a (L := L) (j := j)
    (lam := lam) (D := D) hlam hD
  rw [hfilter] at hcount
  have hcardL : (Finset.range L).card = L := Finset.card_range L
  rw [hcardL] at hcount
  exact False.elim ((not_lt_of_ge hcount) hsize)


/-- Moderate projected bias produces a branch with at least one one-step defect at most `lam`,
provided `lam` is larger than the average defect scale `(1-ρ)/L`. -/
theorem exists_small_branch_step_from_projected_bias
    (b : ℤ → ℂ) (a : ℤ) (L : ℕ) (ρ lam : ℝ)
    (hunit : UnitModulus b)
    (hρ : ρ ≤ projectedTopMean b a L)
    (hlam : 0 < lam)
    (hsize : (1 - ρ) / lam < L) :
    ∃ j < 2^L, ∃ k < L, branchStepDefect b a L j k ≤ lam := by
  rcases greedy_chain_selection_from_moderate_projected_bias b a L ρ hunit hρ with
    ⟨j, hj, hdef⟩
  rcases exists_small_branch_step_of_count_bound b a (L := L) (j := j)
    (lam := lam) (D := 1 - ρ) hlam hdef hsize with ⟨k, hk, hsmall⟩
  exact ⟨j, hj, k, hk, hsmall⟩

/-- A convenient quantitative specialization: taking `lam = 2(1-ρ)/L` yields a dyadic branch
with at least one step whose defect is at most twice the average branch defect. -/
theorem exists_two_average_small_branch_step_from_projected_bias
    (b : ℤ → ℂ) (a : ℤ) (L : ℕ) (ρ : ℝ)
    (hunit : UnitModulus b)
    (hρ : ρ ≤ projectedTopMean b a L)
    (hL : 0 < L)
    (havg : 0 < (2 : ℝ) * (1 - ρ) / L) :
    ∃ j < 2^L, ∃ k < L,
      branchStepDefect b a L j k ≤ (2 : ℝ) * (1 - ρ) / L := by
  have hlam : 0 < (2 : ℝ) * (1 - ρ) / L := havg
  have hLr : 0 < (L : ℝ) := by exact_mod_cast hL
  have hnum : 0 < 1 - ρ := by
    have hmul : 0 < (2 : ℝ) * (1 - ρ) := by
      exact (div_pos_iff_of_pos_right hLr).mp havg
    nlinarith
  have hsize : (1 - ρ) / ((2 : ℝ) * (1 - ρ) / L) < (L : ℝ) := by
    field_simp [hLr.ne', hnum.ne']
    nlinarith [hLr]
  exact exists_small_branch_step_from_projected_bias b a L ρ
    ((2 : ℝ) * (1 - ρ) / L) hunit hρ hlam hsize


/-- A local quadratic obstruction statement. -/
def QuadraticObstruction (liouville : ℤ → ℂ) (I : Finset ℤ) : Prop :=
  ∃ P : ℤ → ℝ,
    (∃ a b c : ℝ, ∀ n, P n = a * (n : ℝ)^2 + b * (n : ℝ) + c) ∧
    1 ≤ ‖∑ n ∈ I, liouville n * eReal (P n)‖

end ProjectedPackets

end FixedShiftLiouville

namespace FixedShiftLiouville
namespace ProjectedPackets

/--
A selected stable scale on a dyadic branch.

This packages the concrete output of the transport-defect counting argument in a reusable form.
-/
def StableBranchScale (b : ℤ → ℂ) (a : ℤ) (L : ℕ) (lam : ℝ) : Prop :=
  ∃ j < 2^L, ∃ k < L, branchStepDefect b a L j k ≤ lam

/-- The previous counting argument already yields a stable branch scale from projected bias. -/
theorem stableBranchScale_of_projected_bias
    (b : ℤ → ℂ) (a : ℤ) (L : ℕ) (ρ lam : ℝ)
    (hunit : UnitModulus b)
    (hρ : ρ ≤ projectedTopMean b a L)
    (hlam : 0 < lam)
    (havg : (1 - ρ) / lam < L) :
    StableBranchScale b a L lam := by
  simpa [StableBranchScale] using
    exists_small_branch_step_from_projected_bias b a L ρ lam hunit hρ hlam havg

/-- A convenient twice-the-average stable-scale consequence of projected bias. -/
theorem stableBranchScale_two_average
    (b : ℤ → ℂ) (a : ℤ) (L : ℕ) (ρ : ℝ)
    (hunit : UnitModulus b)
    (hρ : ρ ≤ projectedTopMean b a L)
    (hL : 0 < L) :
    StableBranchScale b a L ((2 : ℝ) * (1 - ρ) / L) := by
  have htop_le : projectedTopMean b a L ≤ 1 := projectedTopMean_le_one b a L hunit
  have hnum_nonneg : 0 ≤ 1 - ρ := by nlinarith
  by_cases hnum_zero : 1 - ρ = 0
  · have hρeq : ρ = 1 := by linarith
    have htop_ge : 1 ≤ projectedTopMean b a L := by nlinarith
    have htop_eq : projectedTopMean b a L = 1 := le_antisymm htop_le htop_ge
    have hdef0 : projectedTransportDefectAt b a L 0 = 0 := by
      unfold projectedTransportDefectAt projectedTopMean at *
      rw [totalTransportDefect_identity b a hunit L 0]
      have hpow : (0 : ℝ) < 2 ^ L := by positivity
      field_simp [hpow.ne']
      nlinarith
    rcases exists_branchDefect_le_projectedTransportDefectAt b a L 0 with ⟨j, hj, hbj⟩
    have hbranch_le0 : branchDefect b a L 0 j ≤ 0 := by simpa [hdef0] using hbj
    have hbranch_eq0 : branchDefect b a L 0 j = 0 :=
      le_antisymm hbranch_le0 (branchDefect_nonneg b a L 0 j)
    have hsum0 :
        (∑ k ∈ Finset.range L, branchStepDefectAt b a L 0 j k) = 0 := by
      rw [← branchDefect_eq_sum_branchStepDefectAt b a L 0 j, hbranch_eq0]
    have hnonneg : ∀ k ∈ Finset.range L, 0 ≤ branchStepDefectAt b a L 0 j k := by
      intro k hk
      exact branchStepDefectAt_nonneg b a L 0 j k
    have hzero0 : branchStepDefectAt b a L 0 j 0 = 0 := by
      have hz := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum0 0 (by simpa using hL)
      exact hz
    refine ⟨j, hj, 0, hL, ?_⟩
    have hlam0 : ((2 : ℝ) * (1 - ρ) / L) = 0 := by rw [hnum_zero]; ring
    rw [hlam0]
    simpa [branchStepDefect, hzero0]
  · have hnum_pos : 0 < 1 - ρ := lt_of_le_of_ne hnum_nonneg (Ne.symm hnum_zero)
    have hLr : 0 < (L : ℝ) := by exact_mod_cast hL
    have havg : 0 < (2 : ℝ) * (1 - ρ) / L := by positivity
    simpa [StableBranchScale] using
      exists_two_average_small_branch_step_from_projected_bias b a L ρ hunit hρ hL havg

/--
Abstract rigidity input for the remaining part of Section 8.

A sufficiently stable projected branch scale should force a local quadratic obstruction for the
underlying Liouville phase.
-/
def StableScaleRigidityHyp
    (liouville b : ℤ → ℂ) (a : ℤ) (L : ℕ) (lam : ℝ) : Prop :=
  ∀ ⦃j k : ℕ⦄, j < 2^L → k < L → branchStepDefect b a L j k ≤ lam →
    ∃ I : Finset ℤ, QuadraticObstruction liouville I

/--
Projected bias plus stable-scale rigidity gives a quadratic obstruction.
-/
theorem quadratic_obstruction_of_projected_bias
    (liouville b : ℤ → ℂ) (a : ℤ) (L : ℕ) (ρ lam : ℝ)
    (hunit : UnitModulus b)
    (hρ : ρ ≤ projectedTopMean b a L)
    (hlam : 0 < lam)
    (havg : (1 - ρ) / lam < L)
    (hrigidity : StableScaleRigidityHyp liouville b a L lam) :
    ∃ I : Finset ℤ, QuadraticObstruction liouville I := by
  rcases stableBranchScale_of_projected_bias b a L ρ lam hunit hρ hlam havg with
    ⟨j, hj, k, hk, hsmall⟩
  exact hrigidity hj hk hsmall

/--
The twice-the-average stable scale also suffices to force a quadratic obstruction.
-/
theorem quadratic_obstruction_two_average
    (liouville b : ℤ → ℂ) (a : ℤ) (L : ℕ) (ρ : ℝ)
    (hunit : UnitModulus b)
    (hρ : ρ ≤ projectedTopMean b a L)
    (hL : 0 < L)
    (hrigidity : StableScaleRigidityHyp liouville b a L ((2 : ℝ) * (1 - ρ) / L)) :
    ∃ I : Finset ℤ, QuadraticObstruction liouville I := by
  rcases stableBranchScale_two_average b a L ρ hunit hρ hL with
    ⟨j, hj, k, hk, hsmall⟩
  exact hrigidity hj hk hsmall

/--
A paper-shaped final interface for the cleaned Section 8 development.

Once the selector theorem supplies projected top bias and the rigidity theorem converts a stable
branch scale into a quadratic obstruction, the contradiction output is immediate.
-/
def ProjectedBiasQuadraticBridge
    (liouville b : ℤ → ℂ) (a : ℤ) (L : ℕ) (ρ : ℝ) : Prop :=
  ρ ≤ projectedTopMean b a L ∧
  StableScaleRigidityHyp liouville b a L ((2 : ℝ) * (1 - ρ) / L)

/--
Final Section 8 contradiction interface in the cleaned development.
-/
theorem quadratic_obstruction_of_projectedBiasQuadraticBridge
    (liouville b : ℤ → ℂ) (a : ℤ) (L : ℕ) (ρ : ℝ)
    (hunit : UnitModulus b)
    (hL : 0 < L)
    (hbridge : ProjectedBiasQuadraticBridge liouville b a L ρ) :
    ∃ I : Finset ℤ, QuadraticObstruction liouville I := by
  rcases hbridge with ⟨hρ, hrigidity⟩
  exact quadratic_obstruction_two_average liouville b a L ρ hunit hρ hL hrigidity

end ProjectedPackets
end FixedShiftLiouville

/-! ## Section 9: final conditional fixed-shift theorem -/

namespace FixedShiftLiouville

section FinalTheorem

/-- A minimal interface for a Liouville-type sign function on the integers. -/
class LiouvilleLike (Λ : ℤ → ℤ) : Prop where
  abs_le_one : ∀ n : ℤ, |(Λ n : ℝ)| ≤ 1
  sq_one_pos : ∀ n : ℤ, 0 < n → (Λ n) * (Λ n) = 1

/-- The fixed-shift correlation sequence `a_h(n) = Λ(n) Λ(n+h)`. -/
def aShift (Λ : ℤ → ℤ) (h : ℤ) (n : ℕ) : ℝ :=
  (Λ (n : ℤ) : ℝ) * (Λ ((n : ℤ) + h) : ℝ)

/-- The fixed-shift sequence is pointwise bounded by `1` in absolute value. -/
lemma aShift_boundedByOne (Λ : ℤ → ℤ) [LiouvilleLike Λ] (h : ℤ) :
    BoundedByOne (aShift Λ h) := by
  intro n
  unfold aShift
  have h₁ := LiouvilleLike.abs_le_one (Λ := Λ) (n : ℤ)
  have h₂ := LiouvilleLike.abs_le_one (Λ := Λ) ((n : ℤ) + h)
  rw [abs_mul]
  exact mul_le_one₀ h₁ (abs_nonneg _) h₂

/-- On sufficiently large dyadic windows, the fixed-shift sequence takes values in `{±1}`. -/
lemma aShift_squareOneOnWindow
    (Λ : ℤ → ℤ) [LiouvilleLike Λ] (h : ℤ) {X : ℕ}
    (hXpos : 1 ≤ X)
    (hX : Int.natAbs h ≤ X) :
    SquareOneOnWindow (aShift Λ h) X := by
  constructor
  · exact hXpos
  intro n hn
  have hn_low : X + 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hn_pos_nat : 1 ≤ n := by omega
  have hn_pos : 0 < (n : ℤ) := by
    exact_mod_cast hn_pos_nat
  have hX_int : ((Int.natAbs h : ℕ) : ℤ) ≤ X := by
    exact_mod_cast hX
  have hn_int : (X + 1 : ℤ) ≤ n := by
    exact_mod_cast hn_low
  have hh_lower : -((Int.natAbs h : ℤ)) ≤ h := by
    cases h <;> simp <;> omega
  have hnh_pos : 0 < (n : ℤ) + h := by
    omega
  have hsq1_int : (Λ (n : ℤ)) * (Λ (n : ℤ)) = 1 :=
    LiouvilleLike.sq_one_pos (Λ := Λ) (n : ℤ) hn_pos
  have hsq2_int : (Λ ((n : ℤ) + h)) * (Λ ((n : ℤ) + h)) = 1 :=
    LiouvilleLike.sq_one_pos (Λ := Λ) ((n : ℤ) + h) hnh_pos
  have hsq1 : (Λ (n : ℤ) : ℝ) * (Λ (n : ℤ) : ℝ) = 1 := by
    exact_mod_cast hsq1_int
  have hsq2 : (Λ ((n : ℤ) + h) : ℝ) * (Λ ((n : ℤ) + h) : ℝ) = 1 := by
    exact_mod_cast hsq2_int
  unfold aShift
  ring_nf
  nlinarith

/-- The fixed-shift sequence is eventually square-one on every dyadic window. -/
lemma aShift_eventuallySquareOne
    (Λ : ℤ → ℤ) [LiouvilleLike Λ] (h : ℤ) :
    EventuallySquareOne (aShift Λ h) := by
  refine ⟨max 1 (Int.natAbs h), ?_⟩
  intro X hX
  have hXpos : 1 ≤ X := le_trans (le_max_left _ _) hX
  have hXshift : Int.natAbs h ≤ X := le_trans (le_max_right _ _) hX
  exact aShift_squareOneOnWindow Λ h hXpos hXshift

/--
Section 9 final conditional theorem in the cleaned development.

Once the Section 4 coefficient bridge and the Section 6 first-moment hypothesis are available for
`a_h`, the preceding sections imply global prefix cancellation for the fixed-shift sequence.
-/
theorem conditional_fixed_shift_theorem
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (hdom : PositiveDominationCoefficient (aShift Λ h))
    (hfirst : FirstMomentHyp (aShift Λ h)) :
    PrefixLittleO (aShift Λ h) := by
  have hbound : BoundedByOne (aShift Λ h) := aShift_boundedByOne Λ h
  have hsqev : EventuallySquareOne (aShift Λ h) := aShift_eventuallySquareOne Λ h
  exact short_interval_first_moment_theorem hbound hsqev hdom hfirst

/--
A local-`U²` version of the final conditional fixed-shift theorem.

This packages the full Section 7 route for the fixed-shift sequence.
-/
theorem conditional_fixed_shift_theorem_localU2
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (hdom : PositiveDominationCoefficient (aShift Λ h))
    (hblock : LocalU2BlockControl (aShift Λ h))
    (hU2 : LocalU2Hyp (aShift Λ h)) :
    PrefixLittleO (aShift Λ h) := by
  have hbound : BoundedByOne (aShift Λ h) := aShift_boundedByOne Λ h
  have hsqev : EventuallySquareOne (aShift Λ h) := aShift_eventuallySquareOne Λ h
  exact uniform_local_U2_criterion hbound hsqev hdom hblock hU2

end FinalTheorem

end FixedShiftLiouville

/-! ## Section 8 addendum: exact bottleneck interfaces -/

namespace FixedShiftLiouville
namespace ProjectedPackets

/-- Tiny normalized projected transport defect is equivalent to near-total projected top mean. -/
theorem projectedTransportDefect_le_iff
    (b : ℤ → ℂ) (a : ℤ) (L : ℕ) (δ : ℝ)
    (hunit : UnitModulus b) :
    projectedTransportDefect b a L ≤ δ ↔ 1 - δ ≤ projectedTopMean b a L := by
  rw [projectedTransportDefect_eq_one_sub_topMean b a L hunit]
  constructor <;> intro h <;> nlinarith

/-- Near-total projected top mean forces tiny normalized projected transport defect. -/
theorem projectedTransportDefect_le_of_topMean_ge
    (b : ℤ → ℂ) (a : ℤ) (L : ℕ) (δ : ℝ)
    (hunit : UnitModulus b)
    (hmean : 1 - δ ≤ projectedTopMean b a L) :
    projectedTransportDefect b a L ≤ δ := by
  exact (projectedTransportDefect_le_iff b a L δ hunit).2 hmean

/-- Tiny normalized projected transport defect forces near-total projected top mean. -/
theorem topMean_ge_of_projectedTransportDefect_le
    (b : ℤ → ℂ) (a : ℤ) (L : ℕ) (δ : ℝ)
    (hunit : UnitModulus b)
    (hdef : projectedTransportDefect b a L ≤ δ) :
    1 - δ ≤ projectedTopMean b a L := by
  exact (projectedTransportDefect_le_iff b a L δ hunit).1 hdef

/--
A sharp bridge isolating the remaining upgrade in Section 8.

Given a prime slice with a large projected delta packet, this bridge upgrades that information to a
projected top-bias statement strong enough to trigger the cleaned quadratic-obstruction interface.
-/
def ProjectedDeltaToBiasBridge
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ) : Prop :=
  ∀ {p : ℕ}, Nat.Prime p → IntNotDvd p h → p ≤ primeSelectorCutoff I.card →
    (η * (divisibleCount I p : ℝ)) ^ 2 ≤ projectedDeltaPacket a I p α →
      ∃ ρ : ℝ, ∃ a₀ : ℤ, ∃ L : ℕ, 0 < L ∧
        UnitModulus (projectedSignal liouville α h p) ∧
        ProjectedBiasQuadraticBridge liouville (projectedSignal liouville α h p) a₀ L ρ

/--
Section 8 bottleneck packaged in a single theorem.

A small-prime selector gives a large projected delta packet. Any further bridge that upgrades that
packet to projected top bias at some dyadic scale then forces a local quadratic obstruction.
-/
theorem small_prime_selector_to_quadratic_obstruction
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ)
    (hη : 0 ≤ η)
    (hsel : SmallPrimeSliceBiasSelector a h I α η)
    (hbridge : ProjectedDeltaToBiasBridge liouville a h I α η) :
    ∃ J : Finset ℤ, QuadraticObstruction liouville J := by
  rcases small_prime_selector_gives_projected_delta_packet a h I α η hη hsel with
    ⟨p, hp, hph, hcut, hpacket⟩
  rcases hbridge (p := p) hp hph hcut hpacket with ⟨ρ, a₀, L, hL, hunit, hqb⟩
  exact quadratic_obstruction_of_projectedBiasQuadraticBridge liouville
    (projectedSignal liouville α h p) a₀ L ρ hunit hL hqb

/--
A bundled version of the current remaining bottleneck.

The only unproved step in the cleaned Section 8 pipeline is precisely the upgrade from a selected
large projected delta packet to a projected top-bias configuration on some dyadic tree.
-/
def RemainingBottleneckHyp
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ) : Prop :=
  SmallPrimeSliceBiasSelector a h I α η ∧
  ProjectedDeltaToBiasBridge liouville a h I α η

/--
Under the bundled remaining-bottleneck hypothesis, the cleaned Section 8 development already
forces a local quadratic obstruction.
-/
theorem quadratic_obstruction_of_remainingBottleneck
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ)
    (hη : 0 ≤ η)
    (hbottleneck : RemainingBottleneckHyp liouville a h I α η) :
    ∃ J : Finset ℤ, QuadraticObstruction liouville J := by
  rcases hbottleneck with ⟨hsel, hbridge⟩
  exact small_prime_selector_to_quadratic_obstruction liouville a h I α η hη hsel hbridge

end ProjectedPackets
end FixedShiftLiouville

/-! ## Section 8 refinement: replacing projected-bias bridges by transport-defect bridges -/

namespace FixedShiftLiouville
namespace ProjectedPackets

/--
A more concrete replacement for `ProjectedDeltaToBiasBridge`.

Instead of postulating projected top bias directly, this bridge upgrades a large projected delta
packet to a dyadic projected signal with small normalized transport defect. The already-proved
transport identity then converts that defect bound into the bias input needed for the quadratic
obstruction machinery.
-/
def ProjectedDeltaToDefectRigidityBridge
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ) : Prop :=
  ∀ {p : ℕ}, Nat.Prime p → IntNotDvd p h → p ≤ primeSelectorCutoff I.card →
    (η * (divisibleCount I p : ℝ)) ^ 2 ≤ projectedDeltaPacket a I p α →
      ∃ δ : ℝ, ∃ a₀ : ℤ, ∃ L : ℕ, 0 < L ∧
        UnitModulus (projectedSignal liouville α h p) ∧
        projectedTransportDefect (projectedSignal liouville α h p) a₀ L ≤ δ ∧
        StableScaleRigidityHyp liouville (projectedSignal liouville α h p) a₀ L
          (((2 : ℝ) * δ) / L)

/--
The new transport-defect bridge is strong enough to recover the older projected-bias bridge.
-/
theorem projectedDeltaToBiasBridge_of_defectRigidity
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ)
    (hbridge : ProjectedDeltaToDefectRigidityBridge liouville a h I α η) :
    ProjectedDeltaToBiasBridge liouville a h I α η := by
  intro p hp hph hcut hpacket
  rcases hbridge (p := p) hp hph hcut hpacket with ⟨δ, a₀, L, hL, hunit, hdef, hrigidity⟩
  refine ⟨1 - δ, a₀, L, hL, hunit, ?_⟩
  constructor
  · exact topMean_ge_of_projectedTransportDefect_le
      (projectedSignal liouville α h p) a₀ L δ hunit hdef
  · have hparam : ((2 : ℝ) * (1 - (1 - δ)) / L) = (((2 : ℝ) * δ) / L) := by
      ring
    rw [hparam]
    exact hrigidity

/--
Using the more concrete transport-defect bridge, the small-prime selector still forces a local
quadratic obstruction. This theorem replaces the older bias-level bridge hypothesis by a stronger
but more intrinsic input.
-/
theorem small_prime_selector_to_quadratic_obstruction_defect
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ)
    (hη : 0 ≤ η)
    (hsel : SmallPrimeSliceBiasSelector a h I α η)
    (hbridge : ProjectedDeltaToDefectRigidityBridge liouville a h I α η) :
    ∃ J : Finset ℤ, QuadraticObstruction liouville J := by
  have hbridge' : ProjectedDeltaToBiasBridge liouville a h I α η :=
    projectedDeltaToBiasBridge_of_defectRigidity liouville a h I α η hbridge
  exact small_prime_selector_to_quadratic_obstruction liouville a h I α η hη hsel hbridge'

/--
A bundled replacement for `RemainingBottleneckHyp` that uses projected transport defect instead of
projected bias as the intermediate dyadic quantity.
-/
def RemainingBottleneckDefectHyp
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ) : Prop :=
  SmallPrimeSliceBiasSelector a h I α η ∧
  ProjectedDeltaToDefectRigidityBridge liouville a h I α η

/--
The transport-defect bottleneck hypothesis implies the older bias-level bottleneck hypothesis.
-/
theorem remainingBottleneckHyp_of_defect
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ)
    (hbottleneck : RemainingBottleneckDefectHyp liouville a h I α η) :
    RemainingBottleneckHyp liouville a h I α η := by
  rcases hbottleneck with ⟨hsel, hbridge⟩
  exact ⟨hsel, projectedDeltaToBiasBridge_of_defectRigidity liouville a h I α η hbridge⟩

/--
Bundled transport-defect version of the remaining Section 8 bottleneck theorem.
-/
theorem quadratic_obstruction_of_remainingBottleneckDefect
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ)
    (hη : 0 ≤ η)
    (hbottleneck : RemainingBottleneckDefectHyp liouville a h I α η) :
    ∃ J : Finset ℤ, QuadraticObstruction liouville J := by
  rcases hbottleneck with ⟨hsel, hbridge⟩
  exact small_prime_selector_to_quadratic_obstruction_defect liouville a h I α η hη hsel hbridge

end ProjectedPackets
end FixedShiftLiouville


/-! ## Section 8 addendum: bridge-free quadratic interfaces -/

namespace FixedShiftLiouville
namespace ProjectedPackets

/--
A more intrinsic dyadic obstruction interface: instead of recording projected top bias explicitly,
we retain the exact normalized transport-defect bound together with the rigidity input at the
corresponding scale.
-/
def ProjectedDefectQuadraticBridge
    (liouville b : ℤ → ℂ) (a : ℤ) (L : ℕ) (δ : ℝ) : Prop :=
  projectedTransportDefect b a L ≤ δ ∧
  StableScaleRigidityHyp liouville b a L (((2 : ℝ) * δ) / L)

/--
The intrinsic transport-defect bridge recovers the older projected-bias bridge by the exact
transport identity.
-/
theorem projectedBiasQuadraticBridge_of_projectedDefect
    (liouville b : ℤ → ℂ) (a : ℤ) (L : ℕ) (δ : ℝ)
    (hunit : UnitModulus b)
    (hbridge : ProjectedDefectQuadraticBridge liouville b a L δ) :
    ProjectedBiasQuadraticBridge liouville b a L (1 - δ) := by
  rcases hbridge with ⟨hdef, hrigidity⟩
  constructor
  · exact topMean_ge_of_projectedTransportDefect_le b a L δ hunit hdef
  · have hrewrite : 1 - (1 - δ) = δ := by ring
    simpa [hrewrite] using hrigidity

/--
The intrinsic transport-defect bridge is already enough to force a quadratic obstruction.
-/
theorem quadratic_obstruction_of_projectedDefectBridge
    (liouville b : ℤ → ℂ) (a : ℤ) (L : ℕ) (δ : ℝ)
    (hunit : UnitModulus b)
    (hL : 0 < L)
    (hbridge : ProjectedDefectQuadraticBridge liouville b a L δ) :
    ∃ I : Finset ℤ, QuadraticObstruction liouville I := by
  have hbias :
      ProjectedBiasQuadraticBridge liouville b a L (1 - δ) :=
    projectedBiasQuadraticBridge_of_projectedDefect liouville b a L δ hunit hbridge
  exact quadratic_obstruction_of_projectedBiasQuadraticBridge
    liouville b a L (1 - δ) hunit hL hbias

/--
A direct projected-delta-to-quadratic bridge, phrased without any intermediate projected-bias
hypothesis.
-/
def ProjectedDeltaToDefectQuadraticBridge
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ) : Prop :=
  ∀ {p : ℕ}, Nat.Prime p → IntNotDvd p h → p ≤ primeSelectorCutoff I.card →
    (η * (divisibleCount I p : ℝ)) ^ 2 ≤ projectedDeltaPacket a I p α →
      ∃ δ : ℝ, ∃ a₀ : ℤ, ∃ L : ℕ, 0 < L ∧
        UnitModulus (projectedSignal liouville α h p) ∧
        ProjectedDefectQuadraticBridge
          liouville (projectedSignal liouville α h p) a₀ L δ

/--
The earlier transport-defect-and-rigidity bridge automatically yields the more intrinsic direct
quadratic bridge.
-/
theorem projectedDeltaToDefectQuadraticBridge_of_defectRigidity
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ)
    (hbridge : ProjectedDeltaToDefectRigidityBridge liouville a h I α η) :
    ProjectedDeltaToDefectQuadraticBridge liouville a h I α η := by
  intro p hp hph hcut hpacket
  rcases hbridge (p := p) hp hph hcut hpacket with
    ⟨δ, a₀, L, hL, hunit, hdef, hrigidity⟩
  exact ⟨δ, a₀, L, hL, hunit, ⟨hdef, hrigidity⟩⟩

/--
A large projected delta packet together with the direct transport-defect quadratic bridge forces a
quadratic obstruction.
-/
theorem small_prime_selector_to_quadratic_obstruction_intrinsic
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ)
    (hη : 0 ≤ η)
    (hsel : SmallPrimeSliceBiasSelector a h I α η)
    (hbridge : ProjectedDeltaToDefectQuadraticBridge liouville a h I α η) :
    ∃ J : Finset ℤ, QuadraticObstruction liouville J := by
  rcases small_prime_selector_gives_projected_delta_packet a h I α η hη hsel with
    ⟨p, hp, hph, hcut, hpacket⟩
  rcases hbridge (p := p) hp hph hcut hpacket with
    ⟨δ, a₀, L, hL, hunit, hquad⟩
  exact quadratic_obstruction_of_projectedDefectBridge
    liouville (projectedSignal liouville α h p) a₀ L δ hunit hL hquad

/--
A fully intrinsic version of the remaining Section 8 bottleneck: small-prime selection plus a
direct projected-delta-to-transport-defect quadratic bridge.
-/
def RemainingBottleneckIntrinsicHyp
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ) : Prop :=
  SmallPrimeSliceBiasSelector a h I α η ∧
  ProjectedDeltaToDefectQuadraticBridge liouville a h I α η

/--
The defect-rigidity bottleneck implies the intrinsic direct quadratic bottleneck.
-/
theorem remainingBottleneckIntrinsicHyp_of_defect
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ)
    (hbottleneck : RemainingBottleneckDefectHyp liouville a h I α η) :
    RemainingBottleneckIntrinsicHyp liouville a h I α η := by
  rcases hbottleneck with ⟨hsel, hbridge⟩
  exact ⟨hsel,
    projectedDeltaToDefectQuadraticBridge_of_defectRigidity
      liouville a h I α η hbridge⟩

/--
Intrinsic direct quadratic version of the remaining bottleneck theorem.
-/
theorem quadratic_obstruction_of_remainingBottleneckIntrinsic
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ)
    (hη : 0 ≤ η)
    (hbottleneck : RemainingBottleneckIntrinsicHyp liouville a h I α η) :
    ∃ J : Finset ℤ, QuadraticObstruction liouville J := by
  rcases hbottleneck with ⟨hsel, hbridge⟩
  exact small_prime_selector_to_quadratic_obstruction_intrinsic
    liouville a h I α η hη hsel hbridge

end ProjectedPackets
end FixedShiftLiouville

/-! ## Section 8 addendum: selected-prime bridge replacement -/

namespace FixedShiftLiouville
namespace ProjectedPackets

/--
A genuinely weaker selected-prime obstruction witness.

Instead of requiring a delta-to-defect quadratic bridge for every admissible prime below the
selector cutoff, we keep only the one prime actually produced by the small-prime selector together
with the corresponding dyadic quadratic obstruction data.
-/
def SelectedPrimeDefectQuadraticWitness
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ) : Prop :=
  ∃ p : ℕ, Nat.Prime p ∧ IntNotDvd p h ∧ p ≤ primeSelectorCutoff I.card ∧
    η * (divisibleCount I p : ℝ) ≤ ‖divisibleSliceSum a I p α‖ ∧
    ∃ δ : ℝ, ∃ a₀ : ℤ, ∃ L : ℕ, 0 < L ∧
      UnitModulus (projectedSignal liouville α h p) ∧
      ProjectedDefectQuadraticBridge
        liouville (projectedSignal liouville α h p) a₀ L δ

/--
The older intrinsic bottleneck hypothesis implies the weaker selected-prime witness by evaluating
the direct bridge at the prime produced by the selector.
-/
theorem selectedPrimeDefectQuadraticWitness_of_selector_intrinsic
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ)
    (hη : 0 ≤ η)
    (hsel : SmallPrimeSliceBiasSelector a h I α η)
    (hbridge : ProjectedDeltaToDefectQuadraticBridge liouville a h I α η) :
    SelectedPrimeDefectQuadraticWitness liouville a h I α η := by
  rcases hsel with ⟨p, hp, hph, hcut, hbias⟩
  have hpacket :
      (η * (divisibleCount I p : ℝ)) ^ 2 ≤ projectedDeltaPacket a I p α :=
    projected_delta_packet_large_of_slice_bias a I p α η hη hbias
  rcases hbridge (p := p) hp hph hcut hpacket with ⟨δ, a₀, L, hL, hunit, hquad⟩
  exact ⟨p, hp, hph, hcut, hbias, δ, a₀, L, hL, hunit, hquad⟩

/--
A selected-prime witness is already sufficient to force a quadratic obstruction.
-/
theorem quadratic_obstruction_of_selectedPrimeDefectQuadraticWitness
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ)
    (hwitness : SelectedPrimeDefectQuadraticWitness liouville a h I α η) :
    ∃ J : Finset ℤ, QuadraticObstruction liouville J := by
  rcases hwitness with ⟨p, hp, hph, hcut, hbias, δ, a₀, L, hL, hunit, hquad⟩
  exact quadratic_obstruction_of_projectedDefectBridge
    liouville (projectedSignal liouville α h p) a₀ L δ hunit hL hquad

/--
A final selected-prime formulation of the remaining Section 8 bottleneck.

This removes the universal quantification over admissible primes from the end interface and retains
only the single prime actually singled out by the selector.
-/
def RemainingBottleneckSelectedPrimeHyp
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ) : Prop :=
  SelectedPrimeDefectQuadraticWitness liouville a h I α η

/--
The intrinsic bottleneck hypothesis implies the selected-prime bottleneck hypothesis.
-/
theorem remainingBottleneckSelectedPrimeHyp_of_intrinsic
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ)
    (hη : 0 ≤ η)
    (hbottleneck : RemainingBottleneckIntrinsicHyp liouville a h I α η) :
    RemainingBottleneckSelectedPrimeHyp liouville a h I α η := by
  rcases hbottleneck with ⟨hsel, hbridge⟩
  exact selectedPrimeDefectQuadraticWitness_of_selector_intrinsic
    liouville a h I α η hη hsel hbridge

/--
Selected-prime version of the remaining bottleneck theorem.
-/
theorem quadratic_obstruction_of_remainingBottleneckSelectedPrime
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ)
    (hbottleneck : RemainingBottleneckSelectedPrimeHyp liouville a h I α η) :
    ∃ J : Finset ℤ, QuadraticObstruction liouville J := by
  exact quadratic_obstruction_of_selectedPrimeDefectQuadraticWitness
    liouville a h I α η hbottleneck

/--
The earlier defect-based bottleneck also implies the selected-prime bottleneck after passing through
its intrinsic direct-quadratic form.
-/
theorem remainingBottleneckSelectedPrimeHyp_of_defect
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ)
    (hη : 0 ≤ η)
    (hbottleneck : RemainingBottleneckDefectHyp liouville a h I α η) :
    RemainingBottleneckSelectedPrimeHyp liouville a h I α η := by
  have hintrinsic : RemainingBottleneckIntrinsicHyp liouville a h I α η :=
    remainingBottleneckIntrinsicHyp_of_defect liouville a h I α η hbottleneck
  exact remainingBottleneckSelectedPrimeHyp_of_intrinsic
    liouville a h I α η hη hintrinsic

end ProjectedPackets
end FixedShiftLiouville

/-! ## Bridge replacement: threading the weaker Section 4 main-term control forward -/

namespace FixedShiftLiouville

section MainTermBridgeReplacement

/--
The Section 6 first-moment hypothesis already implies the dyadic local quartic hypothesis.

This factors out the purely shell-combinatorial content of Section 6 so that later criteria can be
stated using the weaker Section 4 main-term bridge instead of the stronger coefficient-domination
bridge.
-/
theorem dyadicLocalQuartic_of_firstMoment
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    (hfirst : FirstMomentHyp a) :
    DyadicLocalQuarticHyp a := by
  intro ε hε
  rcases hfirst (ε / 2) (by positivity) with ⟨X₁, hX₁⟩
  rcases criticalScale_sublinear (ε / 2) (by positivity) with ⟨X₂, hX₂⟩
  refine ⟨max X₁ X₂, ?_⟩
  intro X hX k hk u hu
  let H := criticalScale X
  let T : ℕ := u - 2 ^ k + 1
  have hX1 : X₁ ≤ X := le_trans (le_max_left _ _) hX
  have hX2 : X₂ ≤ X := le_trans (le_max_right _ _) hX
  have hkH : k < H := Finset.mem_range.mp (by simpa [H] using hk)
  have hu_low : 2 ^ k ≤ u := (Finset.mem_Icc.mp hu).1
  have hu_high : u ≤ shellTop H k := (Finset.mem_Icc.mp hu).2
  have hu_lt : u < 2 ^ (k + 1) := by
    unfold shellTop at hu_high
    have : u ≤ 2 ^ (k + 1) - 1 := le_trans hu_high (min_le_left _ _)
    have hpowpos : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
    omega
  have hTmem : T ∈ Finset.Icc 1 H := by
    refine Finset.mem_Icc.mpr ?_
    constructor
    · unfold T
      omega
    · have hpow_le : 2 ^ k ≤ H - 1 := by
        exact le_trans hu_low (le_trans hu_high (min_le_right _ _))
      unfold T
      omega
  have hmain :
      ∑ x ∈ Finset.Icc X (2 * X - T), |B a x T| ≤ (ε / 2) * X * T :=
    hX₁ hX1 hTmem
  have hcrit : (H : ℝ) ≤ (ε / 2) * X := hX₂ hX2
  have hTleH : (T : ℝ) ≤ H := by
    exact_mod_cast (Finset.mem_Icc.mp hTmem).2
  have hTsq :
      (T : ℝ)^2 ≤ (ε / 2) * X * 2 ^ k := by
    have hTlepow : (T : ℝ) ≤ 2 ^ k := by
      have : T ≤ 2 ^ k := by
        unfold T
        omega
      exact_mod_cast this
    nlinarith
  have hHleX : H ≤ X := by
    dsimp [H]
    exact criticalScale_le_self X
  have huH : u ≤ H - 1 := le_trans hu_high (min_le_right _ _)
  have huX : u ≤ X := le_trans huH (le_trans (Nat.sub_le H 1) hHleX)
  have hshell := shells_dominated_by_first_moments (a := a) (X := X) ha hu_low hu_lt huX
  dsimp [T] at hshell
  calc
    |Qshell a X k u|
        ≤ ∑ x ∈ Finset.Icc X (2 * X - T), |B a x T| + (T : ℝ)^2 := hshell
    _ ≤ (ε / 2) * X * T + (ε / 2) * X * 2 ^ k := by
          gcongr
    _ ≤ ε * X * 2 ^ k := by
          have hTlepow : (T : ℝ) ≤ 2 ^ k := by
            have : T ≤ 2 ^ k := by
              unfold T
              omega
            exact_mod_cast this
          nlinarith

/--
Section 5 criterion with the weaker Section 4 input.

Once the dyadic local quartic hypothesis yields the positive multiscale bound, the already-proved
main-term form of Section 4 is enough to conclude prefix cancellation.
-/
theorem dyadic_local_quartic_criterion_mainTerm
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    (hsqev : EventuallySquareOne a)
    (hctrl : DirichletMainTermControl a)
    (hdyadic : DyadicLocalQuarticHyp a) :
    PrefixLittleO a := by
  have hmulti : PositiveMultiscaleHyp a :=
    positiveMultiscale_of_dyadicLocalQuartic ha hsqev hdyadic
  exact positive_multiscale_criterion_mainTerm ha hsqev hctrl hmulti

/--
Section 6 theorem with the weaker Section 4 main-term bridge.

This removes the stronger coefficient-domination hypothesis from the Section 6 endgame.
-/
theorem short_interval_first_moment_theorem_mainTerm
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    (hsqev : EventuallySquareOne a)
    (hctrl : DirichletMainTermControl a)
    (hfirst : FirstMomentHyp a) :
    PrefixLittleO a := by
  have hdyadic : DyadicLocalQuarticHyp a :=
    dyadicLocalQuartic_of_firstMoment ha hfirst
  exact dyadic_local_quartic_criterion_mainTerm ha hsqev hctrl hdyadic

/--
Section 7 theorem with the weaker Section 4 main-term bridge.

This shows that the local `U²` route only needs the refined Dirichlet main-term control, not the
stronger coefficient-level domination hypothesis.
-/
theorem uniform_local_U2_criterion_mainTerm
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    (hsqev : EventuallySquareOne a)
    (hctrl : DirichletMainTermControl a)
    (hblock : LocalU2BlockControl a)
    (hU2 : LocalU2Hyp a) :
    PrefixLittleO a := by
  have hfirst : FirstMomentHyp a := firstMoment_of_localU2 hblock hU2
  exact short_interval_first_moment_theorem_mainTerm ha hsqev hctrl hfirst

end MainTermBridgeReplacement

end FixedShiftLiouville

namespace FixedShiftLiouville

section FinalTheoremMainTerm

/--
Section 9 final conditional theorem with the weaker Section 4 main-term bridge.

This replaces the stronger coefficient-domination hypothesis by the refined main-term control.
-/
theorem conditional_fixed_shift_theorem_mainTerm
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (hctrl : DirichletMainTermControl (aShift Λ h))
    (hfirst : FirstMomentHyp (aShift Λ h)) :
    PrefixLittleO (aShift Λ h) := by
  have hbound : BoundedByOne (aShift Λ h) := aShift_boundedByOne Λ h
  have hsqev : EventuallySquareOne (aShift Λ h) := aShift_eventuallySquareOne Λ h
  exact short_interval_first_moment_theorem_mainTerm hbound hsqev hctrl hfirst

/--
A local-`U²` version of the final fixed-shift theorem with the weaker Section 4 input.
-/
theorem conditional_fixed_shift_theorem_localU2_mainTerm
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (hctrl : DirichletMainTermControl (aShift Λ h))
    (hblock : LocalU2BlockControl (aShift Λ h))
    (hU2 : LocalU2Hyp (aShift Λ h)) :
    PrefixLittleO (aShift Λ h) := by
  have hbound : BoundedByOne (aShift Λ h) := aShift_boundedByOne Λ h
  have hsqev : EventuallySquareOne (aShift Λ h) := aShift_eventuallySquareOne Λ h
  exact uniform_local_U2_criterion_mainTerm hbound hsqev hctrl hblock hU2

end FinalTheoremMainTerm

end FixedShiftLiouville


namespace FixedShiftLiouville

section PositiveDominationToMainTerm

/--
A version of the Section 4 main-term control that is only required on windows where `a(n)^2 = 1`.

This is the exact form used later inside the uniform-slope argument, since Section 3 and onward
only ever invoke the main-term estimate on sufficiently large dyadic windows where the eventual
square-one property is already available.
-/
def DirichletMainTermControlOnSquareOne (a : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ X M : ℕ, 1 ≤ M → M ≤ criticalScale X → SquareOneOnWindow a X →
    |dirichletMainTerm a X M - diagonalMass a X|
      ≤ C * (∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2)
        + C * (criticalScale X : ℝ)^2

/--
The uniform-slope argument from Section 4 only needs the Dirichlet main-term control on
square-one windows. This is the honest later-use form of the hypothesis.
-/
theorem uniformSlope_of_dirichletMainTermControlOnSquareOne
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    (hsqev : EventuallySquareOne a)
    (hctrl : DirichletMainTermControlOnSquareOne a)
    (hmulti : PositiveMultiscaleHyp a) :
    UniformSlopeHyp a := by
  rcases dirichlet_increment_representation (a := a) ha with ⟨K, hK, hrepr⟩
  rcases hctrl with ⟨C, hC, hctrlC⟩
  rcases hsqev with ⟨Xsq, hsqall⟩
  intro ε hε
  let C' : ℝ := max (C + K) 1
  have hC'pos : 0 < C' := by
    dsimp [C']
    nlinarith [le_max_right (C + K) 1]
  let η : ℝ := ε / (2 * C')
  have hη : 0 < η := by
    dsimp [η]
    positivity
  rcases hmulti η hη with ⟨X₁, hX₁⟩
  rcases exists_nat_gt ((4 * C') / ε) with ⟨q, hqgt⟩
  have hqpos_real : (0 : ℝ) < q := by
    have hthreshold_pos : (0 : ℝ) < (4 * C') / ε := by
      positivity
    exact lt_trans hthreshold_pos hqgt
  have hq : 1 ≤ q := by
    exact Nat.succ_le_of_lt (Nat.cast_pos.mp hqpos_real)
  rcases eventually_criticalScale_ge q with ⟨X₂, hX₂⟩
  refine ⟨max Xsq (max X₁ X₂), ?_⟩
  intro X M hX hM hMcrit
  have hXsqle : Xsq ≤ X := by
    exact le_trans (le_max_left _ _) hX
  have hX₁le : X₁ ≤ X := by
    exact le_trans (le_trans (le_max_left X₁ X₂) (le_max_right Xsq (max X₁ X₂))) hX
  have hX₂le : X₂ ≤ X := by
    exact le_trans (le_trans (le_max_right X₁ X₂) (le_max_right Xsq (max X₁ X₂))) hX
  have hsq : SquareOneOnWindow a X := hsqall hXsqle
  have hmass : diagonalMass a X = X := diagonalMass_eq_X_of_squareOne hsq
  have hsum :
      ∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2
        ≤ η * X * criticalScale X := by
    exact hX₁ hX₁le
  have hqleH : q ≤ criticalScale X := by
    exact hX₂ hX₂le
  have hqleH_real : (q : ℝ) ≤ criticalScale X := by
    exact_mod_cast hqleH
  have hsum_nonneg :
      0 ≤ ∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2 := by
    refine Finset.sum_nonneg ?_
    intro j hj
    exact div_nonneg (E_nonneg a X j) (sq_nonneg (j : ℝ))
  have hsum_small :
      C' * (∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2)
        ≤ (ε / 2) * X * criticalScale X := by
    have hden : (2 : ℝ) * C' ≠ 0 := by positivity
    have hη_eq : C' * (η * X * criticalScale X) = (ε / 2) * X * criticalScale X := by
      dsimp [η]
      field_simp [hden]
    calc
      C' * (∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2)
          ≤ C' * (η * X * criticalScale X) := by
            exact mul_le_mul_of_nonneg_left hsum (le_of_lt hC'pos)
      _ = (ε / 2) * X * criticalScale X := hη_eq
  have hHbig : (4 * C') / ε < criticalScale X := by
    nlinarith [hqgt, hqleH_real]
  have herror_small :
      2 * C' * (criticalScale X : ℝ)^2 ≤ (ε / 2) * X * criticalScale X := by
    have htmp : 4 * C' < ε * (criticalScale X : ℝ) := by
      have hmul := mul_lt_mul_of_pos_right hHbig hε
      field_simp [ne_of_gt hε] at hmul
      nlinarith
    have hC_small : 2 * C' ≤ (ε / 2) * (criticalScale X : ℝ) := by
      nlinarith
    have hHsq : (criticalScale X : ℝ)^2 ≤ X := by
      exact_mod_cast criticalScale_sq_le X
    have hHnonneg : 0 ≤ (criticalScale X : ℝ) := by positivity
    have hXnonneg : 0 ≤ (X : ℝ) := by positivity
    nlinarith
  have hctrl_main :
      |dirichletMainTerm a X M - diagonalMass a X|
        ≤ C' * (∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2)
          + C' * (criticalScale X : ℝ)^2 := by
    have hmain := hctrlC (X := X) (M := M) hM hMcrit hsq
    have hC_le : C ≤ C' := by
      dsimp [C']
      have h1 : C ≤ C + K := by nlinarith [hK]
      exact le_trans h1 (le_max_left _ _)
    calc
      |dirichletMainTerm a X M - diagonalMass a X|
          ≤ C * (∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2)
            + C * (criticalScale X : ℝ)^2 := hmain
      _ ≤ C' * (∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2)
            + C' * (criticalScale X : ℝ)^2 := by
            exact add_le_add
              (mul_le_mul_of_nonneg_right hC_le hsum_nonneg)
              (mul_le_mul_of_nonneg_right hC_le (sq_nonneg (criticalScale X : ℝ)))
  have hMX : M ≤ X := by
    exact le_trans hMcrit (criticalScale_le_self X)
  have hrepr_main :
      |(E a X (M + 1) - E a X M) - dirichletMainTerm a X M|
        ≤ C' * (criticalScale X : ℝ)^2 := by
    have hmain := hrepr X M hMX hsq
    have hK_le : K ≤ C' := by
      dsimp [C']
      have h1 : K ≤ C + K := by nlinarith [hC]
      exact le_trans h1 (le_max_left _ _)
    have hMcrit_real : (M : ℝ) ≤ criticalScale X := by
      exact_mod_cast hMcrit
    calc
      |(E a X (M + 1) - E a X M) - dirichletMainTerm a X M|
          ≤ K * (M : ℝ)^2 := hmain
      _ ≤ K * (criticalScale X : ℝ)^2 := by
          have hMnonneg : 0 ≤ (M : ℝ) := by positivity
          have hHnonneg : 0 ≤ (criticalScale X : ℝ) := by positivity
          have hMsq : (M : ℝ)^2 ≤ (criticalScale X : ℝ)^2 := by nlinarith
          exact mul_le_mul_of_nonneg_left hMsq hK
      _ ≤ C' * (criticalScale X : ℝ)^2 := by
          exact mul_le_mul_of_nonneg_right hK_le (sq_nonneg (criticalScale X : ℝ))
  calc
    |(E a X (M + 1) - E a X M) - X|
        = |((E a X (M + 1) - E a X M) - dirichletMainTerm a X M)
            + (dirichletMainTerm a X M - diagonalMass a X)| := by
              rw [hmass]
              congr 1
              ring
    _ ≤ |(E a X (M + 1) - E a X M) - dirichletMainTerm a X M|
          + |dirichletMainTerm a X M - diagonalMass a X| := by
            exact abs_add _ _
    _ ≤ C' * (criticalScale X : ℝ)^2
          + (C' * (∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2)
              + C' * (criticalScale X : ℝ)^2) := by
            exact add_le_add hrepr_main hctrl_main
    _ = C' * (∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2)
          + 2 * C' * (criticalScale X : ℝ)^2 := by ring
    _ ≤ (ε / 2) * X * criticalScale X + (ε / 2) * X * criticalScale X := by
          exact add_le_add hsum_small herror_small
    _ ≤ ε * X * criticalScale X := by
          ring_nf
          exact le_rfl

/--
The coefficient-level positive domination hypothesis implies the weaker main-term control on the
square-one windows that the later arguments actually use. This is the first genuine replacement of
a bridge hypothesis in the clean development.
-/
theorem dirichletMainTermControlOnSquareOne_of_positiveDominationCoefficient
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    (hdom : PositiveDominationCoefficient a) :
    DirichletMainTermControlOnSquareOne a := by
  rcases fejer_representation (a := a) ha with ⟨K, hK, hfej⟩
  rcases hdom with ⟨C, hC, hdomC⟩
  let C' : ℝ := max C (C * K)
  have hC'nonneg : 0 ≤ C' := by
    dsimp [C']
    exact le_trans hC (le_max_left _ _)
  refine ⟨C', hC'nonneg, ?_⟩
  intro X M hM hMcrit hsq
  let H := criticalScale X
  let A : ℝ := ∑ j ∈ Finset.Icc 1 H, E a X j / (j : ℝ)^2
  let F : ℝ := ∑ j ∈ Finset.Icc 1 H, fejerMainTerm a X (j - 1) / (j : ℝ)^2
  have hHleX : H ≤ X := criticalScale_le_self X
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    refine Finset.sum_nonneg ?_
    intro j hj
    exact div_nonneg (E_nonneg a X j) (sq_nonneg (j : ℝ))
  have hF_bound :
      F ≤ A + K * (H : ℝ)^2 := by
    dsimp [F, A]
    calc
      ∑ j ∈ Finset.Icc 1 H, fejerMainTerm a X (j - 1) / (j : ℝ)^2
          ≤ ∑ j ∈ Finset.Icc 1 H,
              (E a X j / (j : ℝ)^2 + K * (j : ℝ)) := by
                refine Finset.sum_le_sum ?_
                intro j hj
                have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
                have hjH : j ≤ H := (Finset.mem_Icc.mp hj).2
                have hjm1X : j - 1 ≤ X := by
                  have : j - 1 ≤ H := le_trans (Nat.sub_le j 1) hjH
                  exact le_trans this hHleX
                have hrepr := hfej X (j - 1) hjm1X hsq
                have hjsub : j - 1 + 1 = j := Nat.sub_add_cancel hj1
                have hjcast : (((j - 1 : ℕ) : ℝ) + 1) = (j : ℝ) := by
                  exact_mod_cast hjsub
                have hrepr' :
                    |E a X j - fejerMainTerm a X (j - 1)| ≤ K * (j : ℝ)^3 := by
                  simpa [hjsub, hjcast] using hrepr
                have hterm_raw :
                    fejerMainTerm a X (j - 1) ≤ E a X j + K * (j : ℝ)^3 := by
                  have hlo := (abs_le.mp hrepr').1
                  nlinarith
                have hjpos : 0 < (j : ℝ) := by
                  exact_mod_cast hj1
                have hj2pos : 0 < (j : ℝ)^2 := by positivity
                have hdiv_raw :
                    fejerMainTerm a X (j - 1) / (j : ℝ)^2
                      ≤ (E a X j + K * (j : ℝ)^3) / (j : ℝ)^2 := by
                  exact div_le_div_of_nonneg_right hterm_raw (le_of_lt hj2pos)
                calc
                  fejerMainTerm a X (j - 1) / (j : ℝ)^2
                      ≤ (E a X j + K * (j : ℝ)^3) / (j : ℝ)^2 := hdiv_raw
                  _ = E a X j / (j : ℝ)^2 + K * (j : ℝ) := by
                    field_simp [ne_of_gt hjpos]
      _ = (∑ j ∈ Finset.Icc 1 H, E a X j / (j : ℝ)^2)
          + ∑ j ∈ Finset.Icc 1 H, K * (j : ℝ) := by
            rw [Finset.sum_add_distrib]
      _ = A + K * (∑ j ∈ Finset.Icc 1 H, (j : ℝ)) := by
            dsimp [A]
            rw [← Finset.mul_sum]
      _ ≤ A + K * (H : ℝ)^2 := by
            gcongr
            exact sum_Icc_cast_id_le_sq H
  have hdom_main :
      |dirichletMainTerm a X M - diagonalMass a X| ≤ C * F := by
    dsimp [F]
    exact hdomC X M hM hMcrit
  have hC_le : C ≤ C' := by
    dsimp [C']
    exact le_max_left _ _
  have hCK_le : C * K ≤ C' := by
    dsimp [C']
    exact le_max_right _ _
  calc
    |dirichletMainTerm a X M - diagonalMass a X|
        ≤ C * F := hdom_main
    _ ≤ C * (A + K * (H : ℝ)^2) := by
          exact mul_le_mul_of_nonneg_left hF_bound hC
    _ = C * A + (C * K) * (H : ℝ)^2 := by
          dsimp [A, H]
          ring
    _ ≤ C' * A + C' * (H : ℝ)^2 := by
          exact add_le_add
            (mul_le_mul_of_nonneg_right hC_le hA_nonneg)
            (mul_le_mul_of_nonneg_right hCK_le (sq_nonneg (H : ℝ)))
    _ = C' * (∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2)
          + C' * (criticalScale X : ℝ)^2 := by
          dsimp [A, H]

/--
Re-derived Section 4 uniform slope theorem, now routed through the weaker square-one main-term
control proved from the stronger coefficient-domination hypothesis.
-/
theorem uniformSlope_of_positiveDominationCoefficient_via_mainTerm
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    (hsqev : EventuallySquareOne a)
    (hdom : PositiveDominationCoefficient a)
    (hmulti : PositiveMultiscaleHyp a) :
    UniformSlopeHyp a := by
  have hctrl : DirichletMainTermControlOnSquareOne a :=
    dirichletMainTermControlOnSquareOne_of_positiveDominationCoefficient ha hdom
  exact uniformSlope_of_dirichletMainTermControlOnSquareOne ha hsqev hctrl hmulti

/--
Re-derived Section 4 criterion through the weaker square-one main-term bridge.
-/
theorem positive_multiscale_criterion_via_mainTerm
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    (hsqev : EventuallySquareOne a)
    (hdom : PositiveDominationCoefficient a)
    (hmulti : PositiveMultiscaleHyp a) :
    PrefixLittleO a := by
  apply uniform_slope_criterion (a := a) ha hsqev
  exact uniformSlope_of_positiveDominationCoefficient_via_mainTerm ha hsqev hdom hmulti

/--
Section 6 re-derived through the weaker square-one main-term bridge.
-/
theorem short_interval_first_moment_theorem_via_mainTerm
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    (hsqev : EventuallySquareOne a)
    (hdom : PositiveDominationCoefficient a)
    (hfirst : FirstMomentHyp a) :
    PrefixLittleO a := by
  have hdyadic : DyadicLocalQuarticHyp a := dyadicLocalQuartic_of_firstMoment ha hfirst
  have hmulti : PositiveMultiscaleHyp a :=
    positiveMultiscale_of_dyadicLocalQuartic ha hsqev hdyadic
  exact positive_multiscale_criterion_via_mainTerm ha hsqev hdom hmulti

/--
Section 7 re-derived through the weaker square-one main-term bridge.
-/
theorem uniform_local_U2_criterion_via_mainTerm
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    (hsqev : EventuallySquareOne a)
    (hdom : PositiveDominationCoefficient a)
    (hblock : LocalU2BlockControl a)
    (hU2 : LocalU2Hyp a) :
    PrefixLittleO a := by
  have hfirst : FirstMomentHyp a := firstMoment_of_localU2 hblock hU2
  exact short_interval_first_moment_theorem_via_mainTerm ha hsqev hdom hfirst

/--
Final fixed-shift theorem re-derived through the weaker square-one main-term bridge implied by
the stronger Section 4 coefficient-domination input.
-/
theorem conditional_fixed_shift_theorem_via_mainTerm
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (hdom : PositiveDominationCoefficient (aShift Λ h))
    (hfirst : FirstMomentHyp (aShift Λ h)) :
    PrefixLittleO (aShift Λ h) := by
  have hbound : BoundedByOne (aShift Λ h) := aShift_boundedByOne Λ h
  have hsqev : EventuallySquareOne (aShift Λ h) := aShift_eventuallySquareOne Λ h
  exact short_interval_first_moment_theorem_via_mainTerm hbound hsqev hdom hfirst

/--
Local-`U²` fixed-shift theorem re-derived through the weaker square-one main-term bridge implied
by the stronger Section 4 coefficient-domination input.
-/
theorem conditional_fixed_shift_theorem_localU2_via_mainTerm
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (hdom : PositiveDominationCoefficient (aShift Λ h))
    (hblock : LocalU2BlockControl (aShift Λ h))
    (hU2 : LocalU2Hyp (aShift Λ h)) :
    PrefixLittleO (aShift Λ h) := by
  have hbound : BoundedByOne (aShift Λ h) := aShift_boundedByOne Λ h
  have hsqev : EventuallySquareOne (aShift Λ h) := aShift_eventuallySquareOne Λ h
  exact uniform_local_U2_criterion_via_mainTerm hbound hsqev hdom hblock hU2

end PositiveDominationToMainTerm

end FixedShiftLiouville


/-! ## Section 8 addendum: existential stable-scale rigidity replacement -/

namespace FixedShiftLiouville
namespace ProjectedPackets

/--
A weaker rigidity interface for the projected packet tree.

Instead of demanding a quadratic obstruction from every individual low-defect branch step, we only
ask that the *existence* of a stable branch scale suffices to force such an obstruction.
-/
def StableBranchScaleRigidity
    (liouville b : ℤ → ℂ) (a : ℤ) (L : ℕ) (lam : ℝ) : Prop :=
  StableBranchScale b a L lam → ∃ I : Finset ℤ, QuadraticObstruction liouville I

/--
The older pointwise rigidity hypothesis implies the weaker existential stable-scale rigidity
interface.
-/
theorem stableBranchScaleRigidity_of_pointwise
    (liouville b : ℤ → ℂ) (a : ℤ) (L : ℕ) (lam : ℝ)
    (hrigidity : StableScaleRigidityHyp liouville b a L lam) :
    StableBranchScaleRigidity liouville b a L lam := by
  intro hstable
  rcases hstable with ⟨j, hj, k, hk, hsmall⟩
  exact hrigidity hj hk hsmall

/--
Projected bias together with the weaker existential stable-scale rigidity already forces a
quadratic obstruction.
-/
theorem quadratic_obstruction_of_projected_bias_stable
    (liouville b : ℤ → ℂ) (a : ℤ) (L : ℕ) (ρ lam : ℝ)
    (hunit : UnitModulus b)
    (hρ : ρ ≤ projectedTopMean b a L)
    (hlam : 0 < lam)
    (havg : (1 - ρ) / lam < L)
    (hrigidity : StableBranchScaleRigidity liouville b a L lam) :
    ∃ I : Finset ℤ, QuadraticObstruction liouville I := by
  have hstable : StableBranchScale b a L lam :=
    stableBranchScale_of_projected_bias b a L ρ lam hunit hρ hlam havg
  exact hrigidity hstable

/--
The twice-the-average stable scale likewise suffices under the weaker existential rigidity
interface.
-/
theorem quadratic_obstruction_two_average_stable
    (liouville b : ℤ → ℂ) (a : ℤ) (L : ℕ) (ρ : ℝ)
    (hunit : UnitModulus b)
    (hρ : ρ ≤ projectedTopMean b a L)
    (hL : 0 < L)
    (hrigidity : StableBranchScaleRigidity liouville b a L ((2 : ℝ) * (1 - ρ) / L)) :
    ∃ I : Finset ℤ, QuadraticObstruction liouville I := by
  have hstable : StableBranchScale b a L ((2 : ℝ) * (1 - ρ) / L) :=
    stableBranchScale_two_average b a L ρ hunit hρ hL
  exact hrigidity hstable

/--
A weaker paper-shaped projected-bias bridge using only existential stable-scale rigidity.
-/
def ProjectedBiasQuadraticBridgeStable
    (liouville b : ℤ → ℂ) (a : ℤ) (L : ℕ) (ρ : ℝ) : Prop :=
  ρ ≤ projectedTopMean b a L ∧
  StableBranchScaleRigidity liouville b a L ((2 : ℝ) * (1 - ρ) / L)

/--
The older projected-bias bridge implies the weaker stable-scale bridge.
-/
theorem projectedBiasQuadraticBridgeStable_of_pointwise
    (liouville b : ℤ → ℂ) (a : ℤ) (L : ℕ) (ρ : ℝ)
    (hbridge : ProjectedBiasQuadraticBridge liouville b a L ρ) :
    ProjectedBiasQuadraticBridgeStable liouville b a L ρ := by
  rcases hbridge with ⟨hρ, hrigidity⟩
  refine ⟨hρ, ?_⟩
  exact stableBranchScaleRigidity_of_pointwise liouville b a L ((2 : ℝ) * (1 - ρ) / L) hrigidity

/--
Final Section 8 contradiction interface through the weaker projected-bias bridge.
-/
theorem quadratic_obstruction_of_projectedBiasQuadraticBridgeStable
    (liouville b : ℤ → ℂ) (a : ℤ) (L : ℕ) (ρ : ℝ)
    (hunit : UnitModulus b)
    (hL : 0 < L)
    (hbridge : ProjectedBiasQuadraticBridgeStable liouville b a L ρ) :
    ∃ I : Finset ℤ, QuadraticObstruction liouville I := by
  rcases hbridge with ⟨hρ, hrigidity⟩
  exact quadratic_obstruction_two_average_stable liouville b a L ρ hunit hρ hL hrigidity

/--
A weaker intrinsic transport-defect bridge using only existential stable-scale rigidity.
-/
def ProjectedDefectQuadraticBridgeStable
    (liouville b : ℤ → ℂ) (a : ℤ) (L : ℕ) (δ : ℝ) : Prop :=
  projectedTransportDefect b a L ≤ δ ∧
  StableBranchScaleRigidity liouville b a L (((2 : ℝ) * δ) / L)

/--
The older intrinsic transport-defect bridge implies the weaker existential version.
-/
theorem projectedDefectQuadraticBridgeStable_of_pointwise
    (liouville b : ℤ → ℂ) (a : ℤ) (L : ℕ) (δ : ℝ)
    (hbridge : ProjectedDefectQuadraticBridge liouville b a L δ) :
    ProjectedDefectQuadraticBridgeStable liouville b a L δ := by
  rcases hbridge with ⟨hdef, hrigidity⟩
  refine ⟨hdef, ?_⟩
  exact stableBranchScaleRigidity_of_pointwise liouville b a L (((2 : ℝ) * δ) / L) hrigidity

/--
The weaker intrinsic transport-defect bridge still recovers the projected-bias bridge via the exact
transport identity.
-/
theorem projectedBiasQuadraticBridgeStable_of_projectedDefect
    (liouville b : ℤ → ℂ) (a : ℤ) (L : ℕ) (δ : ℝ)
    (hunit : UnitModulus b)
    (hbridge : ProjectedDefectQuadraticBridgeStable liouville b a L δ) :
    ProjectedBiasQuadraticBridgeStable liouville b a L (1 - δ) := by
  rcases hbridge with ⟨hdef, hrigidity⟩
  constructor
  · exact topMean_ge_of_projectedTransportDefect_le b a L δ hunit hdef
  · have hrewrite : (2 : ℝ) * (1 - (1 - δ)) / L = ((2 : ℝ) * δ) / L := by ring
    simpa [hrewrite] using hrigidity

/--
The weaker intrinsic transport-defect bridge is already enough to force a quadratic obstruction.
-/
theorem quadratic_obstruction_of_projectedDefectBridgeStable
    (liouville b : ℤ → ℂ) (a : ℤ) (L : ℕ) (δ : ℝ)
    (hunit : UnitModulus b)
    (hL : 0 < L)
    (hbridge : ProjectedDefectQuadraticBridgeStable liouville b a L δ) :
    ∃ I : Finset ℤ, QuadraticObstruction liouville I := by
  have hbias :
      ProjectedBiasQuadraticBridgeStable liouville b a L (1 - δ) :=
    projectedBiasQuadraticBridgeStable_of_projectedDefect liouville b a L δ hunit hbridge
  exact quadratic_obstruction_of_projectedBiasQuadraticBridgeStable
    liouville b a L (1 - δ) hunit hL hbias

/--
A selected-prime witness with only the weaker existential stable-scale rigidity retained.
-/
def SelectedPrimeDefectStableWitness
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ) : Prop :=
  ∃ p : ℕ, Nat.Prime p ∧ IntNotDvd p h ∧ p ≤ primeSelectorCutoff I.card ∧
    η * (divisibleCount I p : ℝ) ≤ ‖divisibleSliceSum a I p α‖ ∧
    ∃ δ : ℝ, ∃ a₀ : ℤ, ∃ L : ℕ, 0 < L ∧
      UnitModulus (projectedSignal liouville α h p) ∧
      ProjectedDefectQuadraticBridgeStable
        liouville (projectedSignal liouville α h p) a₀ L δ

/--
The stronger selected-prime witness implies the weaker existential stable-scale witness.
-/
theorem selectedPrimeDefectStableWitness_of_selectedPrimeDefectQuadraticWitness
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ)
    (hwitness : SelectedPrimeDefectQuadraticWitness liouville a h I α η) :
    SelectedPrimeDefectStableWitness liouville a h I α η := by
  rcases hwitness with ⟨p, hp, hph, hcut, hbias, δ, a₀, L, hL, hunit, hquad⟩
  refine ⟨p, hp, hph, hcut, hbias, δ, a₀, L, hL, hunit, ?_⟩
  exact projectedDefectQuadraticBridgeStable_of_pointwise
    liouville (projectedSignal liouville α h p) a₀ L δ hquad

/--
A selected-prime existential stable witness already suffices to force a quadratic obstruction.
-/
theorem quadratic_obstruction_of_selectedPrimeDefectStableWitness
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ)
    (hwitness : SelectedPrimeDefectStableWitness liouville a h I α η) :
    ∃ J : Finset ℤ, QuadraticObstruction liouville J := by
  rcases hwitness with ⟨p, hp, hph, hcut, hbias, δ, a₀, L, hL, hunit, hquad⟩
  exact quadratic_obstruction_of_projectedDefectBridgeStable
    liouville (projectedSignal liouville α h p) a₀ L δ hunit hL hquad

/--
Final selected-prime bottleneck formulated with only existential stable-scale rigidity.
-/
def RemainingBottleneckSelectedPrimeStableHyp
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ) : Prop :=
  SelectedPrimeDefectStableWitness liouville a h I α η

/--
The older selected-prime bottleneck implies the weaker existential stable-scale bottleneck.
-/
theorem remainingBottleneckSelectedPrimeStableHyp_of_selectedPrime
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ)
    (hbottleneck : RemainingBottleneckSelectedPrimeHyp liouville a h I α η) :
    RemainingBottleneckSelectedPrimeStableHyp liouville a h I α η := by
  exact selectedPrimeDefectStableWitness_of_selectedPrimeDefectQuadraticWitness
    liouville a h I α η hbottleneck

/--
The intrinsic and defect-based bottlenecks also imply the weaker existential stable-scale
selected-prime bottleneck.
-/
theorem remainingBottleneckSelectedPrimeStableHyp_of_intrinsic
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ)
    (hη : 0 ≤ η)
    (hbottleneck : RemainingBottleneckIntrinsicHyp liouville a h I α η) :
    RemainingBottleneckSelectedPrimeStableHyp liouville a h I α η := by
  exact remainingBottleneckSelectedPrimeStableHyp_of_selectedPrime
    liouville a h I α η
    (remainingBottleneckSelectedPrimeHyp_of_intrinsic liouville a h I α η hη hbottleneck)

/--
Defect-based route to the weaker existential stable-scale selected-prime bottleneck.
-/
theorem remainingBottleneckSelectedPrimeStableHyp_of_defect
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ)
    (hη : 0 ≤ η)
    (hbottleneck : RemainingBottleneckDefectHyp liouville a h I α η) :
    RemainingBottleneckSelectedPrimeStableHyp liouville a h I α η := by
  exact remainingBottleneckSelectedPrimeStableHyp_of_selectedPrime
    liouville a h I α η
    (remainingBottleneckSelectedPrimeHyp_of_defect liouville a h I α η hη hbottleneck)

/--
Selected-prime theorem through the weaker existential stable-scale bottleneck.
-/
theorem quadratic_obstruction_of_remainingBottleneckSelectedPrimeStable
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ)
    (hbottleneck : RemainingBottleneckSelectedPrimeStableHyp liouville a h I α η) :
    ∃ J : Finset ℤ, QuadraticObstruction liouville J := by
  exact quadratic_obstruction_of_selectedPrimeDefectStableWitness
    liouville a h I α η hbottleneck

end ProjectedPackets
end FixedShiftLiouville

namespace FixedShiftLiouville

section Section4Supremum

/--
A finite-supremum version of the Section 4 Dirichlet-side oscillation over the range `1 ≤ L ≤ H`.
This matches the paper's `sup_{1≤L≤H}` formulation more closely than the pointwise coefficient
control used in earlier passes.
-/
def dirichletOscillationMax (a : ℕ → ℝ) (X H : ℕ) : ℝ :=
  if hH : 1 ≤ H then
    Finset.sup' (Finset.Icc 1 H)
      (by
        refine Finset.nonempty_Icc.mpr ?_
        exact hH)
      (fun L => |dirichletMainTerm a X L - diagonalMass a X|)
  else 0

lemma le_dirichletOscillationMax
    {a : ℕ → ℝ} {X H L : ℕ}
    (hL1 : 1 ≤ L) (hLH : L ≤ H) :
    |dirichletMainTerm a X L - diagonalMass a X| ≤ dirichletOscillationMax a X H := by
  have hH : 1 ≤ H := le_trans hL1 hLH
  unfold dirichletOscillationMax
  rw [dif_pos hH]
  exact Finset.le_sup' (s := Finset.Icc 1 H)
    (f := fun L => |dirichletMainTerm a X L - diagonalMass a X|)
    (b := L) (Finset.mem_Icc.mpr ⟨hL1, hLH⟩)

lemma dirichletOscillationMax_le_of_bound
    {a : ℕ → ℝ} {X H : ℕ} {B : ℝ}
    (hH : 1 ≤ H)
    (hbound : ∀ L : ℕ, 1 ≤ L → L ≤ H →
      |dirichletMainTerm a X L - diagonalMass a X| ≤ B) :
    dirichletOscillationMax a X H ≤ B := by
  unfold dirichletOscillationMax
  rw [dif_pos hH]
  refine Finset.sup'_le (s := Finset.Icc 1 H)
    (H := Finset.nonempty_Icc.mpr hH)
    (f := fun L => |dirichletMainTerm a X L - diagonalMass a X|) ?_
  intro L hL
  exact hbound L (Finset.mem_Icc.mp hL).1 (Finset.mem_Icc.mp hL).2

/--
The coefficient-level positive domination input immediately bounds the Section 4 finite supremum.
-/
theorem dirichletOscillationMax_le_of_positiveDominationCoefficient
    {a : ℕ → ℝ}
    (hdom : PositiveDominationCoefficient a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ,
      dirichletOscillationMax a X (criticalScale X)
        ≤ C * (∑ j ∈ Finset.Icc 1 (criticalScale X), fejerMainTerm a X (j - 1) / (j : ℝ)^2) := by
  rcases hdom with ⟨C, hC, hdomC⟩
  refine ⟨C, hC, ?_⟩
  intro X
  by_cases hX : 1 ≤ X
  · refine dirichletOscillationMax_le_of_bound (a := a) (X := X)
      (H := criticalScale X) (B := C * (∑ j ∈ Finset.Icc 1 (criticalScale X),
        fejerMainTerm a X (j - 1) / (j : ℝ)^2)) (criticalScale_one_le hX) ?_
    intro L hL1 hLH
    exact hdomC X L hL1 hLH
  · have hcrit0 : criticalScale X = 0 := by
      have hX0 : X = 0 := by omega
      simp [criticalScale, hX0]
    unfold dirichletOscillationMax
    rw [hcrit0]
    simp

/--
A supremum-form Section 4 control after converting Fejér coefficients back to the energy profile.
This is the closest clean formal counterpart in the current development to the paper's
`sup_{1≤L≤H}` oscillation estimate.
-/
theorem dirichletOscillationMax_mainTermControl
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    (hdom : PositiveDominationCoefficient a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, SquareOneOnWindow a X →
      dirichletOscillationMax a X (criticalScale X)
        ≤ C * (∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2)
          + C * (criticalScale X : ℝ)^2 := by
  rcases fejer_representation (a := a) ha with ⟨Kfej, hKfej, hfej⟩
  rcases hdom with ⟨C, hC, hdomC⟩
  refine ⟨C + C * Kfej, by nlinarith [hC, hKfej], ?_⟩
  intro X hsq
  have hfej_sum_bound :
      ∑ j ∈ Finset.Icc 1 (criticalScale X), fejerMainTerm a X (j - 1) / (j : ℝ)^2
        ≤ (∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2)
          + Kfej * (criticalScale X : ℝ)^2 := by
    have hsum_step :
        ∑ j ∈ Finset.Icc 1 (criticalScale X), fejerMainTerm a X (j - 1) / (j : ℝ)^2
          ≤ ∑ j ∈ Finset.Icc 1 (criticalScale X), (E a X j / (j : ℝ)^2 + Kfej * (j : ℝ)) := by
      refine Finset.sum_le_sum ?_
      intro j hj
      have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
      have hjH : j ≤ criticalScale X := (Finset.mem_Icc.mp hj).2
      have hmleX : j - 1 ≤ X := by
        have hjm1crit : j - 1 ≤ criticalScale X := le_trans (Nat.sub_le j 1) hjH
        exact le_trans hjm1crit (criticalScale_le_self X)
      have hmain := hfej X (j - 1) hmleX hsq
      have hjsqpos : 0 < (j : ℝ)^2 := by
        have hjpos : (0 : ℝ) < j := by
          exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hj1)
        positivity
      have hupper : fejerMainTerm a X (j - 1) ≤ E a X j + Kfej * (j : ℝ)^3 := by
        have hrew : E a X ((j - 1) + 1) = E a X j := by
          congr
          exact Nat.sub_add_cancel hj1
        rw [hrew] at hmain
        have hpow : (((j - 1 : ℕ) : ℝ) + 1) = (j : ℝ) := by
          exact_mod_cast (Nat.sub_add_cancel hj1)
        rw [hpow] at hmain
        have hlow := (abs_le.mp hmain).1
        nlinarith
      have hdiv : fejerMainTerm a X (j - 1) / (j : ℝ)^2
          ≤ E a X j / (j : ℝ)^2 + Kfej * (j : ℝ) := by
        have htmp : fejerMainTerm a X (j - 1) / (j : ℝ)^2
            ≤ (E a X j + Kfej * (j : ℝ)^3) / (j : ℝ)^2 := by
          exact div_le_div_of_nonneg_right hupper (le_of_lt hjsqpos)
        have hjne : (j : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hj1))
        calc
          fejerMainTerm a X (j - 1) / (j : ℝ)^2
              ≤ (E a X j + Kfej * (j : ℝ)^3) / (j : ℝ)^2 := htmp
          _ = E a X j / (j : ℝ)^2 + Kfej * (j : ℝ) := by
              field_simp [hjne]
      exact hdiv
    have hsum_rearrange :
        ∑ j ∈ Finset.Icc 1 (criticalScale X), (E a X j / (j : ℝ)^2 + Kfej * (j : ℝ))
          = (∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2)
            + Kfej * (∑ j ∈ Finset.Icc 1 (criticalScale X), (j : ℝ)) := by
      rw [Finset.sum_add_distrib]
      rw [← mul_sum (s := Finset.Icc 1 (criticalScale X)) (c := Kfej) (f := fun j => (j : ℝ))]
    have hlin : ∑ j ∈ Finset.Icc 1 (criticalScale X), (j : ℝ) ≤ (criticalScale X : ℝ)^2 :=
      sum_Icc_cast_id_le_sq (criticalScale X)
    calc
      ∑ j ∈ Finset.Icc 1 (criticalScale X), fejerMainTerm a X (j - 1) / (j : ℝ)^2
          ≤ ∑ j ∈ Finset.Icc 1 (criticalScale X), (E a X j / (j : ℝ)^2 + Kfej * (j : ℝ)) := hsum_step
      _ = (∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2)
            + Kfej * (∑ j ∈ Finset.Icc 1 (criticalScale X), (j : ℝ)) := hsum_rearrange
      _ ≤ (∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2)
            + Kfej * (criticalScale X : ℝ)^2 := by
          exact add_le_add_right (mul_le_mul_of_nonneg_left hlin hKfej) _
  have hsupFej :
      dirichletOscillationMax a X (criticalScale X)
        ≤ C * (∑ j ∈ Finset.Icc 1 (criticalScale X), fejerMainTerm a X (j - 1) / (j : ℝ)^2) := by
    refine dirichletOscillationMax_le_of_bound (a := a) (X := X)
      (H := criticalScale X)
      (B := C * (∑ j ∈ Finset.Icc 1 (criticalScale X),
        fejerMainTerm a X (j - 1) / (j : ℝ)^2))
      (criticalScale_one_le hsq.1) ?_
    intro L hL1 hLH
    exact hdomC X L hL1 hLH
  have hsum_nonneg :
      0 ≤ ∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2 := by
    refine Finset.sum_nonneg ?_
    intro j hj
    exact div_nonneg (E_nonneg a X j) (sq_nonneg (j : ℝ))
  calc
    dirichletOscillationMax a X (criticalScale X)
        ≤ C * (∑ j ∈ Finset.Icc 1 (criticalScale X), fejerMainTerm a X (j - 1) / (j : ℝ)^2) := hsupFej
    _ ≤ C * ((∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2)
          + Kfej * (criticalScale X : ℝ)^2) := by
          exact mul_le_mul_of_nonneg_left hfej_sum_bound hC
    _ = C * (∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2)
          + (C * Kfej) * (criticalScale X : ℝ)^2 := by ring
    _ ≤ (C + C * Kfej) * (∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2)
          + (C + C * Kfej) * (criticalScale X : ℝ)^2 := by
          refine add_le_add ?_ ?_
          · have hCle : C ≤ C + C * Kfej := by nlinarith [hC, hKfej]
            exact mul_le_mul_of_nonneg_right hCle hsum_nonneg
          · have hCKle : C * Kfej ≤ C + C * Kfej := by nlinarith [hC, hKfej]
            exact mul_le_mul_of_nonneg_right hCKle (sq_nonneg (criticalScale X : ℝ))

/--
A supremum-form Section 4 criterion. This is equivalent in strength to the earlier pointwise
criterion, but it matches the paper's oscillation statement more closely.
-/
def DirichletOscillationSupControl (a : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, SquareOneOnWindow a X →
    dirichletOscillationMax a X (criticalScale X)
      ≤ C * (∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2)
        + C * (criticalScale X : ℝ)^2

/-- The positive-domination coefficient bridge supplies the supremum-form Section 4 control. -/
theorem dirichletOscillationSupControl_of_positiveDominationCoefficient
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    (hdom : PositiveDominationCoefficient a) :
    DirichletOscillationSupControl a := by
  exact dirichletOscillationMax_mainTermControl (a := a) ha hdom

/--
The supremum-form Section 4 control implies the pointwise main-term control on square-one
windows used in the later reduction chain.
-/
theorem dirichletMainTermControlOnSquareOne_of_sup
    {a : ℕ → ℝ}
    (hsup : DirichletOscillationSupControl a) :
    DirichletMainTermControlOnSquareOne a := by
  rcases hsup with ⟨C, hC, hsupC⟩
  refine ⟨C, hC, ?_⟩
  intro X M hM hMcrit hsq
  have hle : |dirichletMainTerm a X M - diagonalMass a X|
      ≤ dirichletOscillationMax a X (criticalScale X) :=
    le_dirichletOscillationMax (a := a) (X := X) (H := criticalScale X) hM hMcrit
  calc
    |dirichletMainTerm a X M - diagonalMass a X|
        ≤ dirichletOscillationMax a X (criticalScale X) := hle
    _ ≤ C * (∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2)
          + C * (criticalScale X : ℝ)^2 := hsupC X hsq

/--
A paper-shaped Section 4 route: coefficient-level positive domination first yields a supremum
oscillation estimate, and that then feeds the already-completed downstream reduction chain.
-/
theorem positive_multiscale_criterion_sup
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    (hsqev : EventuallySquareOne a)
    (hdom : PositiveDominationCoefficient a)
    (hmulti : PositiveMultiscaleHyp a) :
    PrefixLittleO a := by
  have hsup : DirichletOscillationSupControl a :=
    dirichletOscillationSupControl_of_positiveDominationCoefficient (a := a) ha hdom
  have hctrl : DirichletMainTermControlOnSquareOne a :=
    dirichletMainTermControlOnSquareOne_of_sup (a := a) hsup
  apply uniform_slope_criterion (a := a) ha hsqev
  exact uniformSlope_of_dirichletMainTermControlOnSquareOne ha hsqev hctrl hmulti

end Section4Supremum

end FixedShiftLiouville

namespace FixedShiftLiouville

section Section4SupremumEquivalence

/--
The square-one main-term control is exactly equivalent to the supremum-form oscillation control:
from a pointwise-in-`M` bound on `1 ≤ M ≤ criticalScale X`, one immediately gets the finite
supremum bound by taking the supremum over that same range.
-/
theorem dirichletOscillationSupControl_of_mainTermControlOnSquareOne
    {a : ℕ → ℝ}
    (hctrl : DirichletMainTermControlOnSquareOne a) :
    DirichletOscillationSupControl a := by
  rcases hctrl with ⟨C, hC, hctrlC⟩
  refine ⟨C, hC, ?_⟩
  intro X hsq
  refine dirichletOscillationMax_le_of_bound (a := a) (X := X)
    (H := criticalScale X)
    (B := C * (∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2)
      + C * (criticalScale X : ℝ)^2)
    (criticalScale_one_le hsq.1) ?_
  intro L hL1 hLH
  exact hctrlC X L hL1 hLH hsq

/--
The two clean Section 4 interfaces are equivalent: a pointwise main-term bound on square-one
windows is the same as a bound for the finite supremum of the Dirichlet oscillation.
-/
theorem dirichletOscillationSupControl_iff_mainTermControlOnSquareOne
    {a : ℕ → ℝ} :
    DirichletOscillationSupControl a ↔ DirichletMainTermControlOnSquareOne a := by
  constructor
  · exact dirichletMainTermControlOnSquareOne_of_sup (a := a)
  · exact dirichletOscillationSupControl_of_mainTermControlOnSquareOne (a := a)

/--
The coefficient-level Section 4 bridge can now be routed directly to the square-one main-term
control through the supremum equivalence, rather than being used downstream in a stronger form.
-/
theorem dirichletMainTermControlOnSquareOne_of_positiveDominationCoefficient_via_sup
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    (hdom : PositiveDominationCoefficient a) :
    DirichletMainTermControlOnSquareOne a := by
  have hsup : DirichletOscillationSupControl a :=
    dirichletOscillationSupControl_of_positiveDominationCoefficient (a := a) ha hdom
  exact dirichletMainTermControlOnSquareOne_of_sup (a := a) hsup

/--
A streamlined Section 4 theorem: once the positive-domination coefficient bridge is available,
one may pass immediately to the square-one main-term control and then invoke the existing
uniform-slope mechanism.
-/
theorem positive_multiscale_criterion_squareOneMainTerm
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    (hsqev : EventuallySquareOne a)
    (hdom : PositiveDominationCoefficient a)
    (hmulti : PositiveMultiscaleHyp a) :
    PrefixLittleO a := by
  have hctrl : DirichletMainTermControlOnSquareOne a :=
    dirichletMainTermControlOnSquareOne_of_positiveDominationCoefficient_via_sup
      (a := a) ha hdom
  apply uniform_slope_criterion (a := a) ha hsqev
  exact uniformSlope_of_dirichletMainTermControlOnSquareOne (a := a) ha hsqev hctrl hmulti

end Section4SupremumEquivalence

end FixedShiftLiouville

namespace FixedShiftLiouville

section Section4XMainTerm

/--
A cleaner Section 4 interface on square-one windows: the Dirichlet main term is controlled
relative to `X` itself. On such windows this is equivalent to control relative to the diagonal
mass, since the diagonal mass is exactly `X`.
-/
def DirichletXMainTermControlOnSquareOne (a : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ X M : ℕ, 1 ≤ M → M ≤ criticalScale X → SquareOneOnWindow a X →
    |dirichletMainTerm a X M - X|
      ≤ C * (∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2)
        + C * (criticalScale X : ℝ)^2

/--
On square-one windows, controlling the Dirichlet main term relative to the diagonal mass is the
same as controlling it relative to `X`, because the diagonal mass is exactly `X` there.
-/
theorem dirichletXMainTermControlOnSquareOne_of_mainTermControl
    {a : ℕ → ℝ}
    (hctrl : DirichletMainTermControlOnSquareOne a) :
    DirichletXMainTermControlOnSquareOne a := by
  rcases hctrl with ⟨C, hC, hctrlC⟩
  refine ⟨C, hC, ?_⟩
  intro X M hM hMcrit hsq
  have hmass : diagonalMass a X = X := diagonalMass_eq_X_of_squareOne (a := a) (X := X) hsq
  simpa [hmass] using hctrlC X M hM hMcrit hsq

/--
Conversely, on square-one windows a bound relative to `X` is exactly a bound relative to the
local diagonal mass.
-/
theorem dirichletMainTermControlOnSquareOne_of_XMainTermControl
    {a : ℕ → ℝ}
    (hctrl : DirichletXMainTermControlOnSquareOne a) :
    DirichletMainTermControlOnSquareOne a := by
  rcases hctrl with ⟨C, hC, hctrlC⟩
  refine ⟨C, hC, ?_⟩
  intro X M hM hMcrit hsq
  have hmass : diagonalMass a X = X := diagonalMass_eq_X_of_squareOne (a := a) (X := X) hsq
  simpa [hmass] using hctrlC X M hM hMcrit hsq

/--
The two square-one main-term interfaces are equivalent.
-/
theorem dirichletXMainTermControlOnSquareOne_iff_mainTermControlOnSquareOne
    {a : ℕ → ℝ} :
    DirichletXMainTermControlOnSquareOne a ↔ DirichletMainTermControlOnSquareOne a := by
  constructor
  · exact dirichletMainTermControlOnSquareOne_of_XMainTermControl (a := a)
  · exact dirichletXMainTermControlOnSquareOne_of_mainTermControl (a := a)

/--
The Section 4 coefficient bridge also yields the `|dirichletMainTerm - X|` formulation on
square-one windows.
-/
theorem dirichletXMainTermControlOnSquareOne_of_positiveDominationCoefficient
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    (hdom : PositiveDominationCoefficient a) :
    DirichletXMainTermControlOnSquareOne a := by
  have hctrl : DirichletMainTermControlOnSquareOne a :=
    dirichletMainTermControlOnSquareOne_of_positiveDominationCoefficient_via_sup
      (a := a) ha hdom
  exact dirichletXMainTermControlOnSquareOne_of_mainTermControl (a := a) hctrl

/--
A Section 4 criterion stated directly in the paper-shaped `|dirichletMainTerm - X|` form on
square-one windows.
-/
theorem positive_multiscale_criterion_XMainTerm
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    (hsqev : EventuallySquareOne a)
    (hctrl : DirichletXMainTermControlOnSquareOne a)
    (hmulti : PositiveMultiscaleHyp a) :
    PrefixLittleO a := by
  have hctrl' : DirichletMainTermControlOnSquareOne a :=
    dirichletMainTermControlOnSquareOne_of_XMainTermControl (a := a) hctrl
  apply uniform_slope_criterion (a := a) ha hsqev
  exact uniformSlope_of_dirichletMainTermControlOnSquareOne (a := a) ha hsqev hctrl' hmulti

/--
The positive-domination coefficient bridge can now be routed directly to the paper-shaped
`|dirichletMainTerm - X|` square-one control and then through the existing downstream chain.
-/
theorem positive_multiscale_criterion_XMainTerm_of_positiveDominationCoefficient
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    (hsqev : EventuallySquareOne a)
    (hdom : PositiveDominationCoefficient a)
    (hmulti : PositiveMultiscaleHyp a) :
    PrefixLittleO a := by
  have hctrl : DirichletXMainTermControlOnSquareOne a :=
    dirichletXMainTermControlOnSquareOne_of_positiveDominationCoefficient (a := a) ha hdom
  exact positive_multiscale_criterion_XMainTerm (a := a) ha hsqev hctrl hmulti

end Section4XMainTerm

end FixedShiftLiouville

namespace FixedShiftLiouville

section Section4XSupremum

/--
A paper-shaped finite-supremum Section 4 interface on square-one windows, stated directly in the
form `sup_{1≤L≤H} |dirichletMainTerm(a;X,L) - X|`.
-/
def DirichletXOscillationSupControl (a : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, (hsq : SquareOneOnWindow a X) →
    Finset.sup' (Finset.Icc 1 (criticalScale X))
      (by
        exact Finset.nonempty_Icc.mpr (criticalScale_one_le hsq.1))
      (fun L => |dirichletMainTerm a X L - X|)
      ≤ C * (∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2)
        + C * (criticalScale X : ℝ)^2

/--
On square-one windows, the diagonal-mass supremum control implies the direct `|dirichletMainTerm
- X|` supremum control.
-/
theorem dirichletXOscillationSupControl_of_sup
    {a : ℕ → ℝ}
    (hsup : DirichletOscillationSupControl a) :
    DirichletXOscillationSupControl a := by
  rcases hsup with ⟨C, hC, hsupC⟩
  refine ⟨C, hC, ?_⟩
  intro X hsq
  have hmass : diagonalMass a X = X :=
    diagonalMass_eq_X_of_squareOne (a := a) (X := X) hsq
  have hcongr :
      Finset.sup' (Finset.Icc 1 (criticalScale X))
        (by
          exact Finset.nonempty_Icc.mpr (criticalScale_one_le hsq.1))
        (fun L => |dirichletMainTerm a X L - X|)
      = dirichletOscillationMax a X (criticalScale X) := by
    unfold dirichletOscillationMax
    have hcrit : 1 ≤ criticalScale X := criticalScale_one_le hsq.1
    simp [hcrit, hmass]
  rw [hcongr]
  exact hsupC X hsq

/--
Conversely, the direct `|dirichletMainTerm - X|` supremum control on square-one windows implies
`DirichletOscillationSupControl`.
-/
theorem dirichletOscillationSupControl_of_XSup
    {a : ℕ → ℝ}
    (hsup : DirichletXOscillationSupControl a) :
    DirichletOscillationSupControl a := by
  rcases hsup with ⟨C, hC, hsupC⟩
  refine ⟨C, hC, ?_⟩
  intro X hsq
  have hmass : diagonalMass a X = X :=
    diagonalMass_eq_X_of_squareOne (a := a) (X := X) hsq
  have hcongr :
      dirichletOscillationMax a X (criticalScale X)
      = Finset.sup' (Finset.Icc 1 (criticalScale X))
          (by
            exact Finset.nonempty_Icc.mpr (criticalScale_one_le hsq.1))
          (fun L => |dirichletMainTerm a X L - X|) := by
    unfold dirichletOscillationMax
    have hcrit : 1 ≤ criticalScale X := criticalScale_one_le hsq.1
    simp [hcrit, hmass]
  rw [hcongr]
  exact hsupC X hsq

/--
The two paper-shaped Section 4 supremum interfaces are equivalent on square-one windows.
-/
theorem dirichletXOscillationSupControl_iff_sup
    {a : ℕ → ℝ} :
    DirichletXOscillationSupControl a ↔ DirichletOscillationSupControl a := by
  constructor
  · exact dirichletOscillationSupControl_of_XSup (a := a)
  · exact dirichletXOscillationSupControl_of_sup (a := a)

/--
The direct `|dirichletMainTerm - X|` pointwise square-one control and the corresponding finite
supremum control are equivalent.
-/
theorem dirichletXOscillationSupControl_iff_XMainTermControlOnSquareOne
    {a : ℕ → ℝ} :
    DirichletXOscillationSupControl a ↔ DirichletXMainTermControlOnSquareOne a := by
  constructor
  · intro hsup
    have hsup' : DirichletOscillationSupControl a :=
      dirichletOscillationSupControl_of_XSup (a := a) hsup
    have hmain : DirichletMainTermControlOnSquareOne a :=
      dirichletMainTermControlOnSquareOne_of_sup (a := a) hsup'
    exact dirichletXMainTermControlOnSquareOne_of_mainTermControl (a := a) hmain
  · intro hctrl
    have hmain : DirichletMainTermControlOnSquareOne a :=
      dirichletMainTermControlOnSquareOne_of_XMainTermControl (a := a) hctrl
    have hsup : DirichletOscillationSupControl a :=
      dirichletOscillationSupControl_of_mainTermControlOnSquareOne (a := a) hmain
    exact dirichletXOscillationSupControl_of_sup (a := a) hsup

/--
The Section 4 coefficient bridge also yields the direct `sup |dirichletMainTerm - X|` control on
square-one windows.
-/
theorem dirichletXOscillationSupControl_of_positiveDominationCoefficient
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    (hdom : PositiveDominationCoefficient a) :
    DirichletXOscillationSupControl a := by
  have hsup : DirichletOscillationSupControl a :=
    dirichletOscillationSupControl_of_positiveDominationCoefficient (a := a) ha hdom
  exact dirichletXOscillationSupControl_of_sup (a := a) hsup

/--
A Section 4 criterion routed through the most paper-shaped clean interface currently available:
the finite supremum of `|dirichletMainTerm(a;X,L) - X|` on square-one windows.
-/
theorem positive_multiscale_criterion_XSup
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    (hsqev : EventuallySquareOne a)
    (hsup : DirichletXOscillationSupControl a)
    (hmulti : PositiveMultiscaleHyp a) :
    PrefixLittleO a := by
  have hctrl : DirichletXMainTermControlOnSquareOne a :=
    (dirichletXOscillationSupControl_iff_XMainTermControlOnSquareOne (a := a)).mp hsup
  exact positive_multiscale_criterion_XMainTerm (a := a) ha hsqev hctrl hmulti

/--
The coefficient-level positive-domination bridge can also be routed through the direct
`sup_{1≤L≤H} |dirichletMainTerm - X|` formulation.
-/
theorem positive_multiscale_criterion_XSup_of_positiveDominationCoefficient
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    (hsqev : EventuallySquareOne a)
    (hdom : PositiveDominationCoefficient a)
    (hmulti : PositiveMultiscaleHyp a) :
    PrefixLittleO a := by
  have hsup : DirichletXOscillationSupControl a :=
    dirichletXOscillationSupControl_of_positiveDominationCoefficient (a := a) ha hdom
  exact positive_multiscale_criterion_XSup (a := a) ha hsqev hsup hmulti

end Section4XSupremum

end FixedShiftLiouville

namespace FixedShiftLiouville

section Section4XMaximum

/--
The direct `|dirichletMainTerm(a;X,L) - X|` oscillation maximum up to scale `H`.
This is the finite-supremum quantity that underlies the paper-shaped Section 4 square-one
interfaces.
-/
def dirichletXOscillationMax (a : ℕ → ℝ) (X H : ℕ) : ℝ :=
  if hH : 1 ≤ H then
    Finset.sup' (Finset.Icc 1 H)
      (by
        refine Finset.nonempty_Icc.mpr ?_
        exact hH)
      (fun L => |dirichletMainTerm a X L - X|)
  else 0

lemma le_dirichletXOscillationMax
    {a : ℕ → ℝ} {X H L : ℕ}
    (hL1 : 1 ≤ L) (hLH : L ≤ H) :
    |dirichletMainTerm a X L - X| ≤ dirichletXOscillationMax a X H := by
  have hH : 1 ≤ H := le_trans hL1 hLH
  unfold dirichletXOscillationMax
  rw [dif_pos hH]
  exact Finset.le_sup' (s := Finset.Icc 1 H)
    (f := fun L => |dirichletMainTerm a X L - X|)
    (b := L) (Finset.mem_Icc.mpr ⟨hL1, hLH⟩)

lemma dirichletXOscillationMax_le_of_bound
    {a : ℕ → ℝ} {X H : ℕ} {B : ℝ}
    (hH : 1 ≤ H)
    (hbound : ∀ L : ℕ, 1 ≤ L → L ≤ H → |dirichletMainTerm a X L - X| ≤ B) :
    dirichletXOscillationMax a X H ≤ B := by
  unfold dirichletXOscillationMax
  rw [dif_pos hH]
  refine Finset.sup'_le (s := Finset.Icc 1 H)
    (H := Finset.nonempty_Icc.mpr hH)
    (f := fun L => |dirichletMainTerm a X L - X|) ?_
  intro L hL
  exact hbound L (Finset.mem_Icc.mp hL).1 (Finset.mem_Icc.mp hL).2

/--
On square-one windows, the direct `- X` oscillation maximum and the diagonal-mass oscillation
maximum agree.
-/
lemma dirichletXOscillationMax_eq_dirichletOscillationMax_of_squareOne
    {a : ℕ → ℝ} {X H : ℕ}
    (hsq : SquareOneOnWindow a X) :
    dirichletXOscillationMax a X H = dirichletOscillationMax a X H := by
  unfold dirichletXOscillationMax dirichletOscillationMax
  by_cases hH : 1 ≤ H
  · have hmass : diagonalMass a X = X :=
      diagonalMass_eq_X_of_squareOne (a := a) (X := X) hsq
    simp [hH, hmass]
  · simp [hH]

/--
If the direct Section 4 oscillation maximum exceeds a threshold, then some scale up to `H`
realizes that threshold exceedance.
-/
theorem exists_large_dirichletXOscillationScale
    {a : ℕ → ℝ} {X H : ℕ} {B : ℝ}
    (hH : 1 ≤ H)
    (hgt : B < dirichletXOscillationMax a X H) :
    ∃ L : ℕ, 1 ≤ L ∧ L ≤ H ∧ B < |dirichletMainTerm a X L - X| := by
  by_contra h
  push_neg at h
  have hsuple : dirichletXOscillationMax a X H ≤ B :=
    dirichletXOscillationMax_le_of_bound (a := a) (X := X) (H := H) (B := B) hH h
  exact not_le_of_gt hgt hsuple

/--
Critical-scale specialization of the previous extraction lemma.
-/
theorem exists_large_dirichletXOscillationScale_critical
    {a : ℕ → ℝ} {X : ℕ} {B : ℝ}
    (hX : 1 ≤ X)
    (hgt : B < dirichletXOscillationMax a X (criticalScale X)) :
    ∃ L : ℕ, 1 ≤ L ∧ L ≤ criticalScale X ∧ B < |dirichletMainTerm a X L - X| := by
  exact exists_large_dirichletXOscillationScale
    (a := a) (X := X) (H := criticalScale X) (B := B)
    (criticalScale_one_le hX) hgt

/--
On square-one windows, a large diagonal-mass oscillation at the critical scale yields a scale with
large direct `|dirichletMainTerm - X|` oscillation.
-/
theorem exists_large_dirichletXScale_of_squareOne
    {a : ℕ → ℝ} {X : ℕ} {B : ℝ}
    (hsq : SquareOneOnWindow a X)
    (hgt : B < dirichletOscillationMax a X (criticalScale X)) :
    ∃ L : ℕ, 1 ≤ L ∧ L ≤ criticalScale X ∧ B < |dirichletMainTerm a X L - X| := by
  have hEq :
      dirichletXOscillationMax a X (criticalScale X)
        = dirichletOscillationMax a X (criticalScale X) :=
    dirichletXOscillationMax_eq_dirichletOscillationMax_of_squareOne
      (a := a) (X := X) (H := criticalScale X) hsq
  have hgt' : B < dirichletXOscillationMax a X (criticalScale X) := by
    rw [hEq]
    exact hgt
  exact exists_large_dirichletXOscillationScale_critical (a := a) (X := X) (B := B) hsq.1 hgt'

end Section4XMaximum

end FixedShiftLiouville

namespace FixedShiftLiouville

section LocalU2SummedBridgeReplacement

/--
A weaker Section 7 block input: instead of pointwise control of each short block by its local `U²`
norm, we only require the corresponding summed inequality over the full dyadic window.
-/
def LocalU2SummedBlockControl (a : ℕ → ℝ) : Prop :=
  ∀ ⦃X M : ℕ⦄,
    M ∈ Finset.Icc 1 (criticalScale X) →
      ∑ x ∈ Finset.Icc X (2 * X - M), |B a x M|
        ≤ (M : ℝ) * ∑ x ∈ Finset.Icc X (2 * X - M),
            localU2Norm (natLift a) (zInterval x M)

/--
The original pointwise Section 7 block estimate implies the weaker summed block estimate.
-/
theorem localU2SummedBlockControl_of_pointwise
    {a : ℕ → ℝ}
    (hblock : LocalU2BlockControl a) :
    LocalU2SummedBlockControl a := by
  intro X M hM
  calc
    ∑ x ∈ Finset.Icc X (2 * X - M), |B a x M|
        ≤ ∑ x ∈ Finset.Icc X (2 * X - M),
            (M : ℝ) * localU2Norm (natLift a) (zInterval x M) := by
          refine Finset.sum_le_sum ?_
          intro x hx
          exact hblock hM hx
    _ = (M : ℝ) * ∑ x ∈ Finset.Icc X (2 * X - M),
            localU2Norm (natLift a) (zInterval x M) := by
          rw [mul_sum]

/--
The weaker summed local-`U²` block control still suffices to deduce the Section 6 first-moment
hypothesis from the averaged local `U²` hypothesis.
-/
theorem firstMoment_of_localU2Summed
    {a : ℕ → ℝ}
    (hsummed : LocalU2SummedBlockControl a)
    (hU2 : LocalU2Hyp a) :
    FirstMomentHyp a := by
  intro ε hε
  rcases hU2 ε hε with ⟨X₀, hX₀⟩
  refine ⟨X₀, ?_⟩
  intro X M hX hM
  calc
    ∑ x ∈ Finset.Icc X (2 * X - M), |B a x M|
        ≤ (M : ℝ) * ∑ x ∈ Finset.Icc X (2 * X - M),
            localU2Norm (natLift a) (zInterval x M) := by
          exact hsummed hM
    _ ≤ (M : ℝ) * (ε * X) := by
          gcongr
          exact hX₀ hX hM
    _ = ε * X * M := by ring

/--
Section 7 theorem with the weaker summed local-`U²` block bridge and the weaker Section 4
main-term control.
-/
theorem uniform_local_U2_criterion_summed_mainTerm
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    (hsqev : EventuallySquareOne a)
    (hctrl : DirichletMainTermControl a)
    (hsummed : LocalU2SummedBlockControl a)
    (hU2 : LocalU2Hyp a) :
    PrefixLittleO a := by
  have hfirst : FirstMomentHyp a := firstMoment_of_localU2Summed hsummed hU2
  exact short_interval_first_moment_theorem_mainTerm ha hsqev hctrl hfirst

/--
A positive-domination version of the previous theorem, routed through the Section 4 main-term
control extracted from the stronger coefficient bridge.
-/
theorem uniform_local_U2_criterion_summed_via_mainTerm
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    (hsqev : EventuallySquareOne a)
    (hdom : PositiveDominationCoefficient a)
    (hsummed : LocalU2SummedBlockControl a)
    (hU2 : LocalU2Hyp a) :
    PrefixLittleO a := by
  have hfirst : FirstMomentHyp a := firstMoment_of_localU2Summed hsummed hU2
  exact short_interval_first_moment_theorem_direct ha hfirst

end LocalU2SummedBridgeReplacement

end FixedShiftLiouville

namespace FixedShiftLiouville

section FinalTheoremLocalU2Summed

/--
A summed-local-`U²` version of the final fixed-shift theorem with the weaker Section 4 main-term
bridge.
-/
theorem conditional_fixed_shift_theorem_localU2_summed_mainTerm
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (hctrl : DirichletMainTermControl (aShift Λ h))
    (hsummed : LocalU2SummedBlockControl (aShift Λ h))
    (hU2 : LocalU2Hyp (aShift Λ h)) :
    PrefixLittleO (aShift Λ h) := by
  have hbound : BoundedByOne (aShift Λ h) := aShift_boundedByOne Λ h
  have hsqev : EventuallySquareOne (aShift Λ h) := aShift_eventuallySquareOne Λ h
  exact uniform_local_U2_criterion_summed_mainTerm hbound hsqev hctrl hsummed hU2

/--
A summed-local-`U²` final theorem routed through the stronger positive-domination hypothesis via
Section 4 main-term control.
-/
theorem conditional_fixed_shift_theorem_localU2_summed_via_mainTerm
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (hdom : PositiveDominationCoefficient (aShift Λ h))
    (hsummed : LocalU2SummedBlockControl (aShift Λ h))
    (hU2 : LocalU2Hyp (aShift Λ h)) :
    PrefixLittleO (aShift Λ h) := by
  have hbound : BoundedByOne (aShift Λ h) := aShift_boundedByOne Λ h
  have hsqev : EventuallySquareOne (aShift Λ h) := aShift_eventuallySquareOne Λ h
  exact uniform_local_U2_criterion_summed_via_mainTerm hbound hsqev hdom hsummed hU2

end FinalTheoremLocalU2Summed

end FixedShiftLiouville

namespace FixedShiftLiouville

section DirichletMainTermControlCleanup

/-- A trivial pointwise bound for the quartic correlation sum. -/
lemma abs_P_le
    {a : ℕ → ℝ} (ha : BoundedByOne a) (X t : ℕ) :
    |P a X t| ≤ X := by
  unfold P
  calc
    |∑ n ∈ Finset.Icc (X + 1) (2 * X - t), a n * a (n + t)|
        ≤ ∑ n ∈ Finset.Icc (X + 1) (2 * X - t), |a n * a (n + t)| := by
          simpa using abs_sum_le_sum_abs (fun n => a n * a (n + t))
    _ = ∑ n ∈ Finset.Icc (X + 1) (2 * X - t), |a n| * |a (n + t)| := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          rw [abs_mul]
    _ ≤ ∑ _n ∈ Finset.Icc (X + 1) (2 * X - t), (1 : ℝ) := by
          refine Finset.sum_le_sum ?_
          intro n hn
          have hn0 : 0 ≤ |a n| := abs_nonneg _
          have hnt0 : 0 ≤ |a (n + t)| := abs_nonneg _
          nlinarith [ha n, ha (n + t)]
    _ = ((Finset.Icc (X + 1) (2 * X - t)).card : ℝ) := by
          simp
    _ ≤ ((Finset.Icc (X + 1) (2 * X)).card : ℝ) := by
          have hsubset : Finset.Icc (X + 1) (2 * X - t) ⊆ Finset.Icc (X + 1) (2 * X) := by
            intro n hn
            rcases Finset.mem_Icc.mp hn with ⟨hn1, hn2⟩
            exact Finset.mem_Icc.mpr ⟨hn1, le_trans hn2 (Nat.sub_le _ _)⟩
          exact_mod_cast Finset.card_le_card hsubset
    _ = X := by
          simp
          omega

/-- A trivial Cesàro bound obtained by summing the pointwise quartic bound. -/
lemma abs_C_le
    {a : ℕ → ℝ} (ha : BoundedByOne a) (X M : ℕ) :
    |C a X M| ≤ M * X := by
  unfold C
  calc
    |∑ t ∈ Finset.range M, P a X (t + 1)|
        ≤ ∑ t ∈ Finset.range M, |P a X (t + 1)| := by
          simpa using abs_sum_le_sum_abs (fun t => P a X (t + 1))
    _ ≤ ∑ _t ∈ Finset.range M, (X : ℝ) := by
          refine Finset.sum_le_sum ?_
          intro t ht
          exact abs_P_le ha X (t + 1)
    _ = M * X := by
          simp [mul_comm, mul_left_comm, mul_assoc]

/-- A crude global bound for the Dirichlet-side oscillation. -/
lemma abs_dirichletMainTerm_sub_diagonalMass_le
    {a : ℕ → ℝ} (ha : BoundedByOne a) (X M : ℕ) :
    |dirichletMainTerm a X M - diagonalMass a X| ≤ 2 * M * X := by
  have hC : |C a X M| ≤ M * X := abs_C_le ha X M
  calc
    |dirichletMainTerm a X M - diagonalMass a X|
        = |2 * C a X M| := by
            unfold dirichletMainTerm
            ring_nf
    _ = 2 * |C a X M| := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ 2 * (M * X) := by
          gcongr
    _ = 2 * M * X := by ring

/-- The global Section 4 bridge obviously implies its square-one restriction. -/
theorem dirichletMainTermControlOnSquareOne_of_mainTermControl
    {a : ℕ → ℝ}
    (hctrl : DirichletMainTermControl a) :
    DirichletMainTermControlOnSquareOne a := by
  rcases hctrl with ⟨C, hC, hCprop⟩
  refine ⟨C, hC, ?_⟩
  intro X M hM hMcrit hsq
  exact hCprop X M hM hMcrit

/--
The raw global bridge is not an independent debt item: once we know the Section 4 control on the
square-one windows actually used later, boundedness and eventual square-one let us absorb the
finitely many exceptional small windows into the `H^2` term.
-/
theorem dirichletMainTermControl_of_onSquareOne
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    (hsqev : EventuallySquareOne a)
    (hctrl : DirichletMainTermControlOnSquareOne a) :
    DirichletMainTermControl a := by
  rcases hsqev with ⟨Xsq, hsqall⟩
  rcases hctrl with ⟨C, hC, hCprop⟩
  let C' : ℝ := max C (2 * (Xsq : ℝ)^2)
  have hC'nonneg : 0 ≤ C' := by
    dsimp [C']
    exact le_trans hC (le_max_left _ _)
  refine ⟨C', hC'nonneg, ?_⟩
  intro X M hM hMcrit
  have hsum_nonneg :
      0 ≤ ∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2 := by
    refine Finset.sum_nonneg ?_
    intro j hj
    exact div_nonneg (E_nonneg a X j) (sq_nonneg (j : ℝ))
  by_cases hlarge : Xsq ≤ X
  · have hsq : SquareOneOnWindow a X := hsqall hlarge
    have hmain := hCprop X M hM hMcrit hsq
    have hCle : C ≤ C' := le_max_left _ _
    exact le_trans hmain <| add_le_add
      (mul_le_mul_of_nonneg_right hCle hsum_nonneg)
      (mul_le_mul_of_nonneg_right hCle (sq_nonneg (criticalScale X : ℝ)))
  · have hsmall : X < Xsq := Nat.lt_of_not_ge hlarge
    have hXle : X ≤ Xsq := Nat.le_of_lt hsmall
    have hMleX : M ≤ X := le_trans hMcrit (criticalScale_le_self X)
    have hHpos : 1 ≤ criticalScale X := le_trans hM hMcrit
    have hcrude : |dirichletMainTerm a X M - diagonalMass a X| ≤ 2 * M * X :=
      abs_dirichletMainTerm_sub_diagonalMass_le ha X M
    have hMXbound : 2 * (M : ℝ) * X ≤ 2 * (Xsq : ℝ)^2 := by
      have hMreal : (M : ℝ) ≤ X := by exact_mod_cast hMleX
      have hXreal : (X : ℝ) ≤ Xsq := by exact_mod_cast hXle
      nlinarith
    have hC'large : 2 * (Xsq : ℝ)^2 ≤ C' := le_max_right _ _
    have hHsq1 : (1 : ℝ) ≤ (criticalScale X : ℝ)^2 := by
      have hHreal : (1 : ℝ) ≤ criticalScale X := by exact_mod_cast hHpos
      nlinarith
    have hC'nonneg : 0 ≤ C' := le_trans hC (le_max_left _ _)
    have hbase : |dirichletMainTerm a X M - diagonalMass a X| ≤ C' := by
      have hcrude' : |dirichletMainTerm a X M - diagonalMass a X| ≤ 2 * (M : ℝ) * X := by
        simpa [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using hcrude
      exact le_trans hcrude' (le_trans hMXbound hC'large)
    have hHterm : C' ≤ C' * (criticalScale X : ℝ)^2 := by
      nlinarith
    have hsumterm : C' * (criticalScale X : ℝ)^2
        ≤ C' * (∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2)
          + C' * (criticalScale X : ℝ)^2 := by
      nlinarith
    exact le_trans hbase (le_trans hHterm hsumterm)

/-- With eventual square-one, the raw and restricted Section 4 bridges are equivalent. -/
theorem dirichletMainTermControl_iff_onSquareOne
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    (hsqev : EventuallySquareOne a) :
    DirichletMainTermControl a ↔ DirichletMainTermControlOnSquareOne a := by
  constructor
  · exact dirichletMainTermControlOnSquareOne_of_mainTermControl
  · exact dirichletMainTermControl_of_onSquareOne ha hsqev

/--
Section 5 onward only needs the square-one version of the Section 4 main-term control.
This is the cleaned route that removes `DirichletMainTermControl` from the forward theorem API.
-/
theorem dyadic_local_quartic_criterion_squareOneMainTerm
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    (hsqev : EventuallySquareOne a)
    (hctrl : DirichletMainTermControlOnSquareOne a)
    (hdyadic : DyadicLocalQuarticHyp a) :
    PrefixLittleO a := by
  have hmulti : PositiveMultiscaleHyp a :=
    positiveMultiscale_of_dyadicLocalQuartic ha hsqev hdyadic
  apply uniform_slope_criterion (a := a) ha hsqev
  exact uniformSlope_of_dirichletMainTermControlOnSquareOne ha hsqev hctrl hmulti

/-- Section 6 in cleaned form, using only the square-one Section 4 bridge. -/
theorem short_interval_first_moment_theorem_squareOneMainTerm
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    (hsqev : EventuallySquareOne a)
    (hctrl : DirichletMainTermControlOnSquareOne a)
    (hfirst : FirstMomentHyp a) :
    PrefixLittleO a := by
  have hdyadic : DyadicLocalQuarticHyp a :=
    dyadicLocalQuartic_of_firstMoment ha hfirst
  exact dyadic_local_quartic_criterion_squareOneMainTerm ha hsqev hctrl hdyadic

/-- Section 7 in cleaned summed-block form, using only the square-one Section 4 bridge. -/
theorem uniform_local_U2_criterion_summed_squareOneMainTerm
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    (hsqev : EventuallySquareOne a)
    (hctrl : DirichletMainTermControlOnSquareOne a)
    (hsummed : LocalU2SummedBlockControl a)
    (hU2 : LocalU2Hyp a) :
    PrefixLittleO a := by
  have hfirst : FirstMomentHyp a := firstMoment_of_localU2Summed hsummed hU2
  exact short_interval_first_moment_theorem_squareOneMainTerm ha hsqev hctrl hfirst

/-- Final fixed-shift theorem in cleaned form: no raw `DirichletMainTermControl` remains. -/
theorem conditional_fixed_shift_theorem_localU2_summed_squareOneMainTerm
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (hctrl : DirichletMainTermControlOnSquareOne (aShift Λ h))
    (hsummed : LocalU2SummedBlockControl (aShift Λ h))
    (hU2 : LocalU2Hyp (aShift Λ h)) :
    PrefixLittleO (aShift Λ h) := by
  have hbound : BoundedByOne (aShift Λ h) := aShift_boundedByOne Λ h
  have hsqev : EventuallySquareOne (aShift Λ h) := aShift_eventuallySquareOne Λ h
  exact uniform_local_U2_criterion_summed_squareOneMainTerm hbound hsqev hctrl hsummed hU2

end DirichletMainTermControlCleanup

end FixedShiftLiouville

namespace FixedShiftLiouville

section Section4XSupForwardRoute

/--
Section 5 onward can be routed directly through the paper-shaped Section 4 `sup_{1 ≤ L ≤ H}`
control in the form `|dirichletMainTerm - X|`, without mentioning the diagonal-mass variant.
-/
theorem dyadic_local_quartic_criterion_XSup
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    (hsqev : EventuallySquareOne a)
    (hsup : DirichletXOscillationSupControl a)
    (hdyadic : DyadicLocalQuarticHyp a) :
    PrefixLittleO a := by
  have hmulti : PositiveMultiscaleHyp a :=
    positiveMultiscale_of_dyadicLocalQuartic ha hsqev hdyadic
  exact positive_multiscale_criterion_XSup (a := a) ha hsqev hsup hmulti

/-- Section 6 in the direct Section 4 `sup |Dirichlet - X|` formulation. -/
theorem short_interval_first_moment_theorem_XSup
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    (hsqev : EventuallySquareOne a)
    (hsup : DirichletXOscillationSupControl a)
    (hfirst : FirstMomentHyp a) :
    PrefixLittleO a := by
  have hdyadic : DyadicLocalQuarticHyp a :=
    dyadicLocalQuartic_of_firstMoment ha hfirst
  exact dyadic_local_quartic_criterion_XSup ha hsqev hsup hdyadic

/-- Section 7 in summed-block form, routed through the direct Section 4 `sup |Dirichlet - X|` bridge. -/
theorem uniform_local_U2_criterion_summed_XSup
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    (hsqev : EventuallySquareOne a)
    (hsup : DirichletXOscillationSupControl a)
    (hsummed : LocalU2SummedBlockControl a)
    (hU2 : LocalU2Hyp a) :
    PrefixLittleO a := by
  have hfirst : FirstMomentHyp a :=
    firstMoment_of_localU2Summed hsummed hU2
  exact short_interval_first_moment_theorem_XSup ha hsqev hsup hfirst

/--
Final fixed-shift theorem in the cleanest current Section 4 formulation:
all downstream arguments are routed through the direct finite-supremum bound
`sup_{1 ≤ L ≤ H} |dirichletMainTerm - X|` on square-one windows.
-/
theorem conditional_fixed_shift_theorem_localU2_summed_XSup
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (hsup : DirichletXOscillationSupControl (aShift Λ h))
    (hsummed : LocalU2SummedBlockControl (aShift Λ h))
    (hU2 : LocalU2Hyp (aShift Λ h)) :
    PrefixLittleO (aShift Λ h) := by
  have hbound : BoundedByOne (aShift Λ h) := aShift_boundedByOne Λ h
  have hsqev : EventuallySquareOne (aShift Λ h) := aShift_eventuallySquareOne Λ h
  exact uniform_local_U2_criterion_summed_XSup hbound hsqev hsup hsummed hU2

/--
A compatibility corollary: the stronger coefficient-level positive-domination bridge still feeds
all the way to the final fixed-shift conclusion through the direct `sup |Dirichlet - X|` route.
-/
theorem conditional_fixed_shift_theorem_localU2_summed_XSup_of_positiveDominationCoefficient
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (hdom : PositiveDominationCoefficient (aShift Λ h))
    (hsummed : LocalU2SummedBlockControl (aShift Λ h))
    (hU2 : LocalU2Hyp (aShift Λ h)) :
    PrefixLittleO (aShift Λ h) := by
  have hsup : DirichletXOscillationSupControl (aShift Λ h) :=
    dirichletXOscillationSupControl_of_positiveDominationCoefficient (a := aShift Λ h) (aShift_boundedByOne Λ h) hdom
  exact conditional_fixed_shift_theorem_localU2_summed_XSup Λ h hsup hsummed hU2

end Section4XSupForwardRoute

end FixedShiftLiouville

namespace FixedShiftLiouville

section EventualBridgeWeakening

/--
A weaker Section 4 interface: we only ask for critical-scale max control on sufficiently large
square-one windows.
-/
def EventualDirichletXOscillationMaxControl (a : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, ∃ X₀ : ℕ, 0 ≤ C ∧ ∀ ⦃X : ℕ⦄, X₀ ≤ X → SquareOneOnWindow a X →
    dirichletXOscillationMax a X (criticalScale X)
      ≤ C * (∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2)
        + C * (criticalScale X : ℝ)^2

/--
The global Section 4 `XSup` control implies the weaker eventual critical-scale max control.
-/
theorem eventualDirichletXOscillationMaxControl_of_XSup
    {a : ℕ → ℝ}
    (hsup : DirichletXOscillationSupControl a) :
    EventualDirichletXOscillationMaxControl a := by
  have hctrl : DirichletXMainTermControlOnSquareOne a :=
    (dirichletXOscillationSupControl_iff_XMainTermControlOnSquareOne (a := a)).mp hsup
  rcases hctrl with ⟨C, hC, hctrlC⟩
  refine ⟨C, 0, hC, ?_⟩
  intro X hX hsq
  refine dirichletXOscillationMax_le_of_bound (a := a) (X := X) (H := criticalScale X)
    (B := C * (∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2)
      + C * (criticalScale X : ℝ)^2)
    (criticalScale_one_le hsq.1) ?_
  intro L hL hLcrit
  exact hctrlC X L hL hLcrit hsq

/--
The stronger coefficient-level Section 4 bridge therefore also implies the eventual critical-scale
max control.
-/
theorem eventualDirichletXOscillationMaxControl_of_positiveDominationCoefficient
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    (hdom : PositiveDominationCoefficient a) :
    EventualDirichletXOscillationMaxControl a := by
  have hsup : DirichletXOscillationSupControl a :=
    dirichletXOscillationSupControl_of_positiveDominationCoefficient (a := a) ha hdom
  exact eventualDirichletXOscillationMaxControl_of_XSup (a := a) hsup

/--
An eventual pointwise Section 4 control follows from the eventual critical-scale oscillation-max
control, simply by evaluating the max at a chosen scale `M`.
-/
def EventualDirichletXMainTermControlOnSquareOne (a : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, ∃ X₀ : ℕ, 0 ≤ C ∧ ∀ ⦃X M : ℕ⦄, X₀ ≤ X →
    1 ≤ M → M ≤ criticalScale X → SquareOneOnWindow a X →
      |dirichletMainTerm a X M - X|
        ≤ C * (∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2)
          + C * (criticalScale X : ℝ)^2

/--
The eventual critical-scale max control implies the eventual pointwise square-one control.
-/
theorem eventualDirichletXMainTermControlOnSquareOne_of_max
    {a : ℕ → ℝ}
    (hmax : EventualDirichletXOscillationMaxControl a) :
    EventualDirichletXMainTermControlOnSquareOne a := by
  rcases hmax with ⟨C, X₀, hC, hmaxC⟩
  refine ⟨C, X₀, hC, ?_⟩
  intro X M hX hM hMcrit hsq
  have hle : |dirichletMainTerm a X M - X|
      ≤ dirichletXOscillationMax a X (criticalScale X) :=
    le_dirichletXOscillationMax (a := a) (X := X) (H := criticalScale X) hM hMcrit
  exact le_trans hle (hmaxC hX hsq)

/--
The eventual pointwise square-one Section 4 control is enough for the uniform-slope step; only
sufficiently large dyadic windows are ever used later.
-/
theorem uniformSlope_of_eventualDirichletXMainTermControlOnSquareOne
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    (hsqev : EventuallySquareOne a)
    (hctrl : EventualDirichletXMainTermControlOnSquareOne a)
    (hmulti : PositiveMultiscaleHyp a) :
    UniformSlopeHyp a := by
  rcases dirichlet_increment_representation (a := a) ha with ⟨K, hK, hrepr⟩
  rcases hctrl with ⟨C, Xctrl, hC, hctrlC⟩
  rcases hsqev with ⟨Xsq, hsqall⟩
  intro ε hε
  let C' : ℝ := max (C + K) 1
  have hC'pos : 0 < C' := by
    dsimp [C']
    nlinarith [le_max_right (C + K) 1]
  let η : ℝ := ε / (2 * C')
  have hη : 0 < η := by
    dsimp [η]
    positivity
  rcases hmulti η hη with ⟨X₁, hX₁⟩
  rcases exists_nat_gt ((4 * C') / ε) with ⟨q, hqgt⟩
  have hqpos_real : (0 : ℝ) < q := by
    have hthreshold_pos : (0 : ℝ) < (4 * C') / ε := by
      positivity
    exact lt_trans hthreshold_pos hqgt
  have hq : 1 ≤ q := by
    exact Nat.succ_le_of_lt (Nat.cast_pos.mp hqpos_real)
  rcases eventually_criticalScale_ge q with ⟨X₂, hX₂⟩
  refine ⟨max Xctrl (max Xsq (max X₁ X₂)), ?_⟩
  intro X M hX hM hMcrit
  have hXctrlle : Xctrl ≤ X := by
    exact le_trans (le_max_left _ _) hX
  have htail : max Xsq (max X₁ X₂) ≤ X := le_trans (le_max_right _ _) hX
  have hXsqle : Xsq ≤ X := le_trans (le_max_left _ _) htail
  have htail2 : max X₁ X₂ ≤ X := le_trans (le_max_right _ _) htail
  have hX₁le : X₁ ≤ X := le_trans (le_max_left _ _) htail2
  have hX₂le : X₂ ≤ X := le_trans (le_max_right _ _) htail2
  have hsq : SquareOneOnWindow a X := hsqall hXsqle
  have hsum :
      ∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2
        ≤ η * X * criticalScale X := by
    exact hX₁ hX₁le
  have hqleH : q ≤ criticalScale X := by
    exact hX₂ hX₂le
  have hqleH_real : (q : ℝ) ≤ criticalScale X := by
    exact_mod_cast hqleH
  have hsum_nonneg :
      0 ≤ ∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2 := by
    refine Finset.sum_nonneg ?_
    intro j hj
    exact div_nonneg (E_nonneg a X j) (sq_nonneg (j : ℝ))
  have hsum_small :
      C' * (∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2)
        ≤ (ε / 2) * X * criticalScale X := by
    have hden : (2 : ℝ) * C' ≠ 0 := by positivity
    have hη_eq : C' * (η * X * criticalScale X) = (ε / 2) * X * criticalScale X := by
      dsimp [η]
      field_simp [hden]
    calc
      C' * (∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2)
          ≤ C' * (η * X * criticalScale X) := by
            exact mul_le_mul_of_nonneg_left hsum (le_of_lt hC'pos)
      _ = (ε / 2) * X * criticalScale X := hη_eq
  have hHbig : (4 * C') / ε < criticalScale X := by
    nlinarith [hqgt, hqleH_real]
  have herror_small :
      2 * C' * (criticalScale X : ℝ)^2 ≤ (ε / 2) * X * criticalScale X := by
    have htmp : 4 * C' < ε * (criticalScale X : ℝ) := by
      have hmul := mul_lt_mul_of_pos_right hHbig hε
      field_simp [ne_of_gt hε] at hmul
      nlinarith
    have hC_small : 2 * C' ≤ (ε / 2) * (criticalScale X : ℝ) := by
      nlinarith
    have hHsq : (criticalScale X : ℝ)^2 ≤ X := by
      exact_mod_cast criticalScale_sq_le X
    have hHnonneg : 0 ≤ (criticalScale X : ℝ) := by positivity
    have hXnonneg : 0 ≤ (X : ℝ) := by positivity
    nlinarith
  have hctrl_main :
      |dirichletMainTerm a X M - X|
        ≤ C' * (∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2)
          + C' * (criticalScale X : ℝ)^2 := by
    have hmain := hctrlC (X := X) (M := M) hXctrlle hM hMcrit hsq
    have hC_le : C ≤ C' := by
      dsimp [C']
      have h1 : C ≤ C + K := by nlinarith [hK]
      exact le_trans h1 (le_max_left _ _)
    calc
      |dirichletMainTerm a X M - X|
          ≤ C * (∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2)
            + C * (criticalScale X : ℝ)^2 := hmain
      _ ≤ C' * (∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2)
            + C' * (criticalScale X : ℝ)^2 := by
            exact add_le_add
              (mul_le_mul_of_nonneg_right hC_le hsum_nonneg)
              (mul_le_mul_of_nonneg_right hC_le (sq_nonneg (criticalScale X : ℝ)))
  have hMX : M ≤ X := by
    exact le_trans hMcrit (criticalScale_le_self X)
  have hrepr_main :
      |(E a X (M + 1) - E a X M) - dirichletMainTerm a X M|
        ≤ C' * (criticalScale X : ℝ)^2 := by
    have hmain := hrepr X M hMX hsq
    have hK_le : K ≤ C' := by
      dsimp [C']
      have h1 : K ≤ C + K := by nlinarith [hC]
      exact le_trans h1 (le_max_left _ _)
    have hMcrit_real : (M : ℝ) ≤ criticalScale X := by
      exact_mod_cast hMcrit
    calc
      |(E a X (M + 1) - E a X M) - dirichletMainTerm a X M|
          ≤ K * (M : ℝ)^2 := hmain
      _ ≤ K * (criticalScale X : ℝ)^2 := by
          have hMnonneg : 0 ≤ (M : ℝ) := by positivity
          have hHnonneg : 0 ≤ (criticalScale X : ℝ) := by positivity
          have hMsq : (M : ℝ)^2 ≤ (criticalScale X : ℝ)^2 := by nlinarith
          exact mul_le_mul_of_nonneg_left hMsq hK
      _ ≤ C' * (criticalScale X : ℝ)^2 := by
          exact mul_le_mul_of_nonneg_right hK_le (sq_nonneg (criticalScale X : ℝ))
  calc
    |(E a X (M + 1) - E a X M) - X|
        = |((E a X (M + 1) - E a X M) - dirichletMainTerm a X M)
            + (dirichletMainTerm a X M - X)| := by
              congr 1
              ring
    _ ≤ |(E a X (M + 1) - E a X M) - dirichletMainTerm a X M|
          + |dirichletMainTerm a X M - X| := by
            exact abs_add _ _
    _ ≤ C' * (criticalScale X : ℝ)^2
          + (C' * (∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2)
              + C' * (criticalScale X : ℝ)^2) := by
            exact add_le_add hrepr_main hctrl_main
    _ = C' * (∑ j ∈ Finset.Icc 1 (criticalScale X), E a X j / (j : ℝ)^2)
          + 2 * C' * (criticalScale X : ℝ)^2 := by ring
    _ ≤ (ε / 2) * X * criticalScale X + (ε / 2) * X * criticalScale X := by
          exact add_le_add hsum_small herror_small
    _ ≤ ε * X * criticalScale X := by
          ring_nf
          exact le_rfl

/--
A weaker Section 7 bridge: we only require the summed block inequality for sufficiently large
windows.
-/
def EventualLocalU2SummedBlockControl (a : ℕ → ℝ) : Prop :=
  ∃ X₀ : ℕ, ∀ ⦃X M : ℕ⦄, X₀ ≤ X →
    M ∈ Finset.Icc 1 (criticalScale X) →
      ∑ x ∈ Finset.Icc X (2 * X - M), |B a x M|
        ≤ (M : ℝ) * ∑ x ∈ Finset.Icc X (2 * X - M),
            localU2Norm (natLift a) (zInterval x M)

/--
The global summed block bridge implies the weaker eventual version.
-/
theorem eventualLocalU2SummedBlockControl_of_global
    {a : ℕ → ℝ}
    (hsummed : LocalU2SummedBlockControl a) :
    EventualLocalU2SummedBlockControl a := by
  refine ⟨0, ?_⟩
  intro X M hX hM
  exact hsummed hM

/--
The eventual summed block bridge is enough to recover the Section 6 first-moment hypothesis from
local `U²` control.
-/
theorem firstMoment_of_eventualLocalU2Summed
    {a : ℕ → ℝ}
    (hsummed : EventualLocalU2SummedBlockControl a)
    (hU2 : LocalU2Hyp a) :
    FirstMomentHyp a := by
  intro ε hε
  rcases hsummed with ⟨Xsum, hsumall⟩
  rcases hU2 ε hε with ⟨X₁, hX₁⟩
  refine ⟨max Xsum X₁, ?_⟩
  intro X M hX hM
  have hXsumle : Xsum ≤ X := by
    exact le_trans (le_max_left _ _) hX
  have hX₁le : X₁ ≤ X := by
    exact le_trans (le_max_right _ _) hX
  calc
    ∑ x ∈ Finset.Icc X (2 * X - M), |B a x M|
        ≤ (M : ℝ) * ∑ x ∈ Finset.Icc X (2 * X - M),
            localU2Norm (natLift a) (zInterval x M) := by
          exact hsumall hXsumle hM
    _ ≤ (M : ℝ) * (ε * X) := by
          gcongr
          exact hX₁ hX₁le hM
    _ = ε * X * M := by ring

/--
Section 4 onward can now be routed through the weakest current Section 4 input: eventual critical-
scale oscillation-max control on square-one windows.
-/
theorem positive_multiscale_criterion_eventualXMax
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    (hsqev : EventuallySquareOne a)
    (hmax : EventualDirichletXOscillationMaxControl a)
    (hmulti : PositiveMultiscaleHyp a) :
    PrefixLittleO a := by
  have hctrl : EventualDirichletXMainTermControlOnSquareOne a :=
    eventualDirichletXMainTermControlOnSquareOne_of_max (a := a) hmax
  apply uniform_slope_criterion (a := a) ha hsqev
  exact uniformSlope_of_eventualDirichletXMainTermControlOnSquareOne (a := a) ha hsqev hctrl hmulti

/--
Section 6 routed through the eventual Section 4 critical-scale max control.
-/
theorem short_interval_first_moment_theorem_eventualXMax
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    (hsqev : EventuallySquareOne a)
    (hmax : EventualDirichletXOscillationMaxControl a)
    (hfirst : FirstMomentHyp a) :
    PrefixLittleO a := by
  have hdyadic : DyadicLocalQuarticHyp a :=
    dyadicLocalQuartic_of_firstMoment ha hfirst
  have hmulti : PositiveMultiscaleHyp a :=
    positiveMultiscale_of_dyadicLocalQuartic ha hsqev hdyadic
  exact positive_multiscale_criterion_eventualXMax (a := a) ha hsqev hmax hmulti

/--
Section 7 routed through the weakest current Section 4 and Section 7 bridge assumptions.
-/
theorem uniform_local_U2_criterion_eventual_summed_XMax
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    (hsqev : EventuallySquareOne a)
    (hmax : EventualDirichletXOscillationMaxControl a)
    (hsummed : EventualLocalU2SummedBlockControl a)
    (hU2 : LocalU2Hyp a) :
    PrefixLittleO a := by
  have hfirst : FirstMomentHyp a :=
    firstMoment_of_eventualLocalU2Summed (a := a) hsummed hU2
  exact short_interval_first_moment_theorem_eventualXMax (a := a) ha hsqev hmax hfirst

/--
Final fixed-shift theorem routed through the weakest current Section 4 and Section 7 bridge
interfaces: eventual critical-scale max control and eventual summed local-`U²` block control.
-/
theorem conditional_fixed_shift_theorem_localU2_eventual_summed_XMax
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (hmax : EventualDirichletXOscillationMaxControl (aShift Λ h))
    (hsummed : EventualLocalU2SummedBlockControl (aShift Λ h))
    (hU2 : LocalU2Hyp (aShift Λ h)) :
    PrefixLittleO (aShift Λ h) := by
  have hbound : BoundedByOne (aShift Λ h) := aShift_boundedByOne Λ h
  have hsqev : EventuallySquareOne (aShift Λ h) := aShift_eventuallySquareOne Λ h
  exact uniform_local_U2_criterion_eventual_summed_XMax (a := aShift Λ h)
    hbound hsqev hmax hsummed hU2

/--
Compatibility corollary: the older stronger Section 4 and Section 7 bridges still imply the new
weakest current final fixed-shift theorem.
-/
theorem conditional_fixed_shift_theorem_localU2_eventual_summed_XMax_of_positiveDominationCoefficient
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (hdom : PositiveDominationCoefficient (aShift Λ h))
    (hsummed : LocalU2SummedBlockControl (aShift Λ h))
    (hU2 : LocalU2Hyp (aShift Λ h)) :
    PrefixLittleO (aShift Λ h) := by
  have hbound : BoundedByOne (aShift Λ h) := aShift_boundedByOne Λ h
  have hmax : EventualDirichletXOscillationMaxControl (aShift Λ h) :=
    eventualDirichletXOscillationMaxControl_of_positiveDominationCoefficient
      (a := aShift Λ h) hbound hdom
  have hsummed' : EventualLocalU2SummedBlockControl (aShift Λ h) :=
    eventualLocalU2SummedBlockControl_of_global (a := aShift Λ h) hsummed
  exact conditional_fixed_shift_theorem_localU2_eventual_summed_XMax Λ h hmax hsummed' hU2

end EventualBridgeWeakening


section RemainingDebtMinimization

/--
The weakest current forward-chain assumptions for a general bounded sequence:
eventual critical-scale Section 4 control, eventual summed Section 7 block control,
and the genuine local `U²` hypothesis.
-/
def MinimalMainForwardHyp (a : ℕ → ℝ) : Prop :=
  EventualDirichletXOscillationMaxControl a ∧
  EventualLocalU2SummedBlockControl a ∧
  LocalU2Hyp a

/--
Under boundedness and eventual square-one, the weakest current forward-chain assumptions imply
global prefix cancellation.
-/
theorem prefixLittleO_of_minimalMainForwardHyp
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    (hsqev : EventuallySquareOne a)
    (hmin : MinimalMainForwardHyp a) :
    PrefixLittleO a := by
  rcases hmin with ⟨hmax, hsummed, hU2⟩
  exact uniform_local_U2_criterion_eventual_summed_XMax
    (a := a) ha hsqev hmax hsummed hU2

/--
The older stronger Section 4 and Section 7 bridges imply the weakest current forward-chain
hypothesis.
-/
theorem minimalMainForwardHyp_of_positiveDominationCoefficient
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    (hdom : PositiveDominationCoefficient a)
    (hsummed : LocalU2SummedBlockControl a)
    (hU2 : LocalU2Hyp a) :
    MinimalMainForwardHyp a := by
  refine ⟨?_, ?_, hU2⟩
  · exact eventualDirichletXOscillationMaxControl_of_positiveDominationCoefficient
      (a := a) ha hdom
  · exact eventualLocalU2SummedBlockControl_of_global (a := a) hsummed

/--
The weakest current forward-chain assumptions, specialized to the fixed-shift sequence.
-/
def MinimalFixedShiftMainHyp
    (Λ : ℤ → ℤ) [LiouvilleLike Λ] (h : ℤ) : Prop :=
  MinimalMainForwardHyp (aShift Λ h)

/--
Minimal fixed-shift theorem through the weakest current forward-chain assumptions.
-/
theorem conditional_fixed_shift_theorem_minimal
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (hmin : MinimalFixedShiftMainHyp Λ h) :
    PrefixLittleO (aShift Λ h) := by
  have hbound : BoundedByOne (aShift Λ h) := aShift_boundedByOne Λ h
  have hsqev : EventuallySquareOne (aShift Λ h) := aShift_eventuallySquareOne Λ h
  exact prefixLittleO_of_minimalMainForwardHyp
    (a := aShift Λ h) hbound hsqev hmin

/--
Compatibility corollary: the older stronger forward-chain assumptions imply the new minimal
fixed-shift hypothesis.
-/
theorem minimalFixedShiftMainHyp_of_positiveDominationCoefficient
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (hdom : PositiveDominationCoefficient (aShift Λ h))
    (hsummed : LocalU2SummedBlockControl (aShift Λ h))
    (hU2 : LocalU2Hyp (aShift Λ h)) :
    MinimalFixedShiftMainHyp Λ h := by
  have hbound : BoundedByOne (aShift Λ h) := aShift_boundedByOne Λ h
  exact minimalMainForwardHyp_of_positiveDominationCoefficient
    (a := aShift Λ h) hbound hdom hsummed hU2

/--
The weakest current Section 8 endgame bottleneck:
a selected prime with a stable-scale projected-defect witness.
-/
def MinimalSection8EndgameHyp
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ) : Prop :=
  ProjectedPackets.RemainingBottleneckSelectedPrimeStableHyp liouville a h I α η

/--
The weakest current Section 8 endgame bottleneck already forces a quadratic obstruction.
-/
theorem quadratic_obstruction_of_minimalSection8EndgameHyp
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ)
    (hmin : MinimalSection8EndgameHyp liouville a h I α η) :
    ∃ J : Finset ℤ, QuadraticObstruction liouville J := by
  exact ProjectedPackets.quadratic_obstruction_of_remainingBottleneckSelectedPrimeStable
    liouville a h I α η hmin

/--
Any older selected-prime, intrinsic, or defect-style Section 8 bottleneck implies the new minimal
endgame bottleneck.
-/
theorem minimalSection8EndgameHyp_of_selectedPrime
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ)
    (hbottleneck : ProjectedPackets.RemainingBottleneckSelectedPrimeHyp liouville a h I α η) :
    MinimalSection8EndgameHyp liouville a h I α η := by
  exact ProjectedPackets.remainingBottleneckSelectedPrimeStableHyp_of_selectedPrime
    liouville a h I α η hbottleneck

theorem minimalSection8EndgameHyp_of_intrinsic
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ)
    (hη : 0 ≤ η)
    (hbottleneck : ProjectedPackets.RemainingBottleneckIntrinsicHyp liouville a h I α η) :
    MinimalSection8EndgameHyp liouville a h I α η := by
  exact ProjectedPackets.remainingBottleneckSelectedPrimeStableHyp_of_intrinsic
    liouville a h I α η hη hbottleneck

theorem minimalSection8EndgameHyp_of_defect
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ)
    (hη : 0 ≤ η)
    (hbottleneck : ProjectedPackets.RemainingBottleneckDefectHyp liouville a h I α η) :
    MinimalSection8EndgameHyp liouville a h I α η := by
  exact ProjectedPackets.remainingBottleneckSelectedPrimeStableHyp_of_defect
    liouville a h I α η hη hbottleneck

end RemainingDebtMinimization

end FixedShiftLiouville

/-! ## Pass 43 addendum: direct paper-to-minimal forward aliases and explicit selector/rigidity residue -/

namespace FixedShiftLiouville

section Pass43ForwardAliases

/--
The paper-shaped square-one control `|dirichletMainTerm - X|` already implies the current weakest
Section 4 interface after passing to the critical-scale finite maximum.
-/
theorem eventualDirichletXOscillationMaxControl_of_XMainTermControlOnSquareOne
    {a : ℕ → ℝ}
    (hctrl : DirichletXMainTermControlOnSquareOne a) :
    EventualDirichletXOscillationMaxControl a := by
  have hsup : DirichletXOscillationSupControl a :=
    (dirichletXOscillationSupControl_iff_XMainTermControlOnSquareOne (a := a)).mpr hctrl
  exact eventualDirichletXOscillationMaxControl_of_XSup (a := a) hsup

/--
Likewise, the diagonal-mass square-one control from earlier passes implies the current weakest
Section 4 interface.
-/
theorem eventualDirichletXOscillationMaxControl_of_mainTermControlOnSquareOne
    {a : ℕ → ℝ}
    (hctrl : DirichletMainTermControlOnSquareOne a) :
    EventualDirichletXOscillationMaxControl a := by
  have hctrlX : DirichletXMainTermControlOnSquareOne a :=
    dirichletXMainTermControlOnSquareOne_of_mainTermControl (a := a) hctrl
  exact eventualDirichletXOscillationMaxControl_of_XMainTermControlOnSquareOne
    (a := a) hctrlX

/--
The original pointwise Section 7 block estimate implies the current weakest eventual summed block
interface.
-/
theorem eventualLocalU2SummedBlockControl_of_pointwise
    {a : ℕ → ℝ}
    (hblock : LocalU2BlockControl a) :
    EventualLocalU2SummedBlockControl a := by
  have hsummed : LocalU2SummedBlockControl a :=
    localU2SummedBlockControl_of_pointwise (a := a) hblock
  exact eventualLocalU2SummedBlockControl_of_global (a := a) hsummed

/--
The original stronger paper-style Section 4 and Section 7 inputs imply the current minimal forward
hypothesis.
-/
theorem minimalMainForwardHyp_of_positiveDominationCoefficient_pointwise
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    (hdom : PositiveDominationCoefficient a)
    (hblock : LocalU2BlockControl a)
    (hU2 : LocalU2Hyp a) :
    MinimalMainForwardHyp a := by
  have hsummed : LocalU2SummedBlockControl a :=
    localU2SummedBlockControl_of_pointwise (a := a) hblock
  exact minimalMainForwardHyp_of_positiveDominationCoefficient
    (a := a) ha hdom hsummed hU2

/--
Fixed-shift specialization of the previous alias: the older pointwise Section 7 block estimate and
coefficient-level Section 4 bridge already imply the current minimal fixed-shift forward
hypothesis.
-/
theorem minimalFixedShiftMainHyp_of_positiveDominationCoefficient_pointwise
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (hdom : PositiveDominationCoefficient (aShift Λ h))
    (hblock : LocalU2BlockControl (aShift Λ h))
    (hU2 : LocalU2Hyp (aShift Λ h)) :
    MinimalFixedShiftMainHyp Λ h := by
  have hbound : BoundedByOne (aShift Λ h) := aShift_boundedByOne Λ h
  exact minimalMainForwardHyp_of_positiveDominationCoefficient_pointwise
    (a := aShift Λ h) hbound hdom hblock hU2

/--
Direct paper-to-minimal final theorem: the older coefficient-domination and pointwise local-`U²`
block inputs already feed the current weakest fixed-shift forward theorem.
-/
theorem conditional_fixed_shift_theorem_minimal_of_positiveDominationCoefficient_pointwise
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (hdom : PositiveDominationCoefficient (aShift Λ h))
    (hblock : LocalU2BlockControl (aShift Λ h))
    (hU2 : LocalU2Hyp (aShift Λ h)) :
    PrefixLittleO (aShift Λ h) := by
  exact conditional_fixed_shift_theorem_minimal Λ h
    (minimalFixedShiftMainHyp_of_positiveDominationCoefficient_pointwise
      Λ h hdom hblock hU2)

end Pass43ForwardAliases

end FixedShiftLiouville

namespace FixedShiftLiouville
namespace ProjectedPackets

section Pass43SelectorRigidityResidue

/--
A stable-scale version of the projected-delta bridge.

This packages the exact remaining Section 8 selector/rigidity content in the weakest form currently
used by the formalization: for any admissible selected prime with a large projected delta packet,
one can reach a dyadic projected signal together with the existential stable-scale transport-defect
bridge needed for quadratic obstruction.
-/
def ProjectedDeltaToDefectStableBridge
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ) : Prop :=
  ∀ {p : ℕ}, Nat.Prime p → IntNotDvd p h → p ≤ primeSelectorCutoff I.card →
    (η * (divisibleCount I p : ℝ)) ^ 2 ≤ projectedDeltaPacket a I p α →
      ∃ δ : ℝ, ∃ a₀ : ℤ, ∃ L : ℕ, 0 < L ∧
        UnitModulus (projectedSignal liouville α h p) ∧
        ProjectedDefectQuadraticBridgeStable
          liouville (projectedSignal liouville α h p) a₀ L δ

/--
The stronger intrinsic direct quadratic bridge implies the weaker stable-scale bridge by weakening
the projected dyadic conclusion.
-/
theorem projectedDeltaToDefectStableBridge_of_intrinsic
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ)
    (hbridge : ProjectedDeltaToDefectQuadraticBridge liouville a h I α η) :
    ProjectedDeltaToDefectStableBridge liouville a h I α η := by
  intro p hp hph hcut hpacket
  rcases hbridge (p := p) hp hph hcut hpacket with ⟨δ, a₀, L, hL, hunit, hquad⟩
  refine ⟨δ, a₀, L, hL, hunit, ?_⟩
  exact projectedDefectQuadraticBridgeStable_of_pointwise
    liouville (projectedSignal liouville α h p) a₀ L δ hquad

/--
Evaluating the stable-scale bridge at the prime selected by the small-prime selector yields the
current weakest selected-prime stable witness.
-/
theorem selectedPrimeDefectStableWitness_of_selector_stableBridge
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ)
    (hη : 0 ≤ η)
    (hsel : SmallPrimeSliceBiasSelector a h I α η)
    (hbridge : ProjectedDeltaToDefectStableBridge liouville a h I α η) :
    SelectedPrimeDefectStableWitness liouville a h I α η := by
  rcases hsel with ⟨p, hp, hph, hcut, hbias⟩
  have hpacket :
      (η * (divisibleCount I p : ℝ)) ^ 2 ≤ projectedDeltaPacket a I p α :=
    projected_delta_packet_large_of_slice_bias a I p α η hη hbias
  rcases hbridge (p := p) hp hph hcut hpacket with ⟨δ, a₀, L, hL, hunit, hstable⟩
  exact ⟨p, hp, hph, hcut, hbias, δ, a₀, L, hL, hunit, hstable⟩

/--
An explicit packaging of the residual Section 8 selector/rigidity content.

This is the paper-faithful bottleneck underneath the current endgame hypothesis: a small-prime
selector together with a bridge from the resulting large projected packet to a stable dyadic
transport-defect witness.
-/
def RemainingBottleneckSelectorRigidityStableHyp
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ) : Prop :=
  SmallPrimeSliceBiasSelector a h I α η ∧
  ProjectedDeltaToDefectStableBridge liouville a h I α η

/--
The explicit selector/rigidity bottleneck implies the current weakest selected-prime stable
endgame interface.
-/
theorem remainingBottleneckSelectedPrimeStableHyp_of_selectorRigidityStable
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ)
    (hη : 0 ≤ η)
    (hbottleneck : RemainingBottleneckSelectorRigidityStableHyp liouville a h I α η) :
    RemainingBottleneckSelectedPrimeStableHyp liouville a h I α η := by
  rcases hbottleneck with ⟨hsel, hbridge⟩
  exact selectedPrimeDefectStableWitness_of_selector_stableBridge
    liouville a h I α η hη hsel hbridge

/--
Hence the explicit selector/rigidity residue already forces a quadratic obstruction.
-/
theorem quadratic_obstruction_of_remainingBottleneckSelectorRigidityStable
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ)
    (hη : 0 ≤ η)
    (hbottleneck : RemainingBottleneckSelectorRigidityStableHyp liouville a h I α η) :
    ∃ J : Finset ℤ, QuadraticObstruction liouville J := by
  have hstable : RemainingBottleneckSelectedPrimeStableHyp liouville a h I α η :=
    remainingBottleneckSelectedPrimeStableHyp_of_selectorRigidityStable
      liouville a h I α η hη hbottleneck
  exact quadratic_obstruction_of_remainingBottleneckSelectedPrimeStable
    liouville a h I α η hstable

/--
The older intrinsic direct quadratic bottleneck already contains the explicit selector/rigidity
stable bottleneck.
-/
theorem remainingBottleneckSelectorRigidityStableHyp_of_intrinsic
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ)
    (hbottleneck : RemainingBottleneckIntrinsicHyp liouville a h I α η) :
    RemainingBottleneckSelectorRigidityStableHyp liouville a h I α η := by
  rcases hbottleneck with ⟨hsel, hbridge⟩
  exact ⟨hsel,
    projectedDeltaToDefectStableBridge_of_intrinsic liouville a h I α η hbridge⟩

end Pass43SelectorRigidityResidue

end ProjectedPackets
end FixedShiftLiouville

/-! ## Pass 44 addendum: isolate the genuinely unproved paper debt -/

namespace FixedShiftLiouville

section Pass44ActualDebtInterfaces

/--
The true remaining Section 4 analytic core in the current development.

Passes 42–43 already show that this stronger paper-shaped coefficient domination hypothesis implies
all later weakened Section 4 interfaces, including eventual critical-scale oscillation-max control.
So if one asks what is still genuinely unproved rather than merely still assumed downstream, this is
exactly the remaining Section 4 core.
-/
def Section4AnalyticCoreHyp (a : ℕ → ℝ) : Prop :=
  PositiveDominationCoefficient a

/--
The true remaining Section 7 block estimate in the current development.

Pass 43 already derives the eventual summed block interface from this pointwise local `U²` block
bound, so this is the actual unresolved Section 7 statement rather than a downstream weakening.
-/
def Section7BlockEstimateHyp (a : ℕ → ℝ) : Prop :=
  LocalU2BlockControl a

/--
The explicit remaining Section 8 selector/rigidity content.

This is the paper-faithful endgame residue isolated in pass 43: a small-prime selector together
with a bridge from the resulting projected delta packet to the stable-scale transport-defect
witness needed for quadratic obstruction.
-/
def Section8SelectorRigidityCoreHyp
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ) : Prop :=
  ProjectedPackets.RemainingBottleneckSelectorRigidityStableHyp liouville a h I α η

/--
The actual remaining Section 4 core implies the current weakest Section 4 forward interface.
-/
theorem eventualDirichletXOscillationMaxControl_of_section4AnalyticCore
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    (hsec4 : Section4AnalyticCoreHyp a) :
    EventualDirichletXOscillationMaxControl a := by
  exact eventualDirichletXOscillationMaxControl_of_positiveDominationCoefficient
    (a := a) ha hsec4

/--
The actual remaining Section 7 block estimate implies the current weakest Section 7 forward
interface.
-/
theorem eventualLocalU2SummedBlockControl_of_section7BlockEstimate
    {a : ℕ → ℝ}
    (hsec7 : Section7BlockEstimateHyp a) :
    EventualLocalU2SummedBlockControl a := by
  exact eventualLocalU2SummedBlockControl_of_pointwise (a := a) hsec7

/--
The actual remaining Section 8 selector/rigidity core implies the current weakest endgame
interface.
-/
theorem remainingBottleneckSelectedPrimeStableHyp_of_section8SelectorRigidityCore
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ)
    (hη : 0 ≤ η)
    (hsec8 : Section8SelectorRigidityCoreHyp liouville a h I α η) :
    ProjectedPackets.RemainingBottleneckSelectedPrimeStableHyp liouville a h I α η := by
  exact ProjectedPackets.remainingBottleneckSelectedPrimeStableHyp_of_selectorRigidityStable
    liouville a h I α η hη hsec8

/--
Bundled statement of the genuine remaining forward debt after the reductions already formalized in
passes 1–43.

The Section 4 core is the coefficient-domination bridge, the Section 7 core is the pointwise local
`U²` block estimate, and the local averaged `U²` input remains as before.
-/
def ActualRemainingForwardDebt (a : ℕ → ℝ) : Prop :=
  Section4AnalyticCoreHyp a ∧ Section7BlockEstimateHyp a ∧ LocalU2Hyp a

/--
Bundled statement of the genuine remaining endgame debt after the reductions already formalized in
passes 1–43.
-/
def ActualRemainingEndgameDebt
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ) : Prop :=
  Section8SelectorRigidityCoreHyp liouville a h I α η

/--
The genuine remaining forward debt already implies the current minimal forward interface.
-/
theorem minimalMainForwardHyp_of_actualRemainingForwardDebt
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    (hdebt : ActualRemainingForwardDebt a) :
    MinimalMainForwardHyp a := by
  rcases hdebt with ⟨hsec4, hsec7, hU2⟩
  refine ⟨?_, ?_, hU2⟩
  · exact eventualDirichletXOscillationMaxControl_of_section4AnalyticCore (a := a) ha hsec4
  · exact eventualLocalU2SummedBlockControl_of_section7BlockEstimate (a := a) hsec7

/--
Fixed-shift specialization: the genuinely remaining forward paper debt implies prefix
cancellation.
-/
theorem conditional_fixed_shift_theorem_of_actualRemainingForwardDebt
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (hdebt : ActualRemainingForwardDebt (aShift Λ h)) :
    PrefixLittleO (aShift Λ h) := by
  have hbound : BoundedByOne (aShift Λ h) := aShift_boundedByOne Λ h
  exact conditional_fixed_shift_theorem_minimal Λ h
    (minimalMainForwardHyp_of_actualRemainingForwardDebt
      (a := aShift Λ h) hbound hdebt)

/--
The genuine remaining Section 8 endgame debt already forces a quadratic obstruction.
-/
theorem quadratic_obstruction_of_actualRemainingEndgameDebt
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ)
    (hη : 0 ≤ η)
    (hdebt : ActualRemainingEndgameDebt liouville a h I α η) :
    ∃ J : Finset ℤ, QuadraticObstruction liouville J := by
  exact ProjectedPackets.quadratic_obstruction_of_remainingBottleneckSelectorRigidityStable
    liouville a h I α η hη hdebt

/--
A single bundled package recording the genuinely remaining paper debt in the current formalization.

This does not solve the analytic bottlenecks; it isolates them exactly. Everything downstream of
this package is now formalized in Lean.
-/
def ActualRemainingPaperDebt
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (liouville a : ℤ → ℂ) (I : Finset ℤ) (α η : ℝ) : Prop :=
  ActualRemainingForwardDebt (aShift Λ h) ∧
  ActualRemainingEndgameDebt liouville a h I α η

/--
From the single bundled remaining paper debt package one gets both the forward fixed-shift theorem
and the Section 8 quadratic obstruction output.
-/
theorem consequences_of_actualRemainingPaperDebt
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (liouville a : ℤ → ℂ) (I : Finset ℤ) (α η : ℝ)
    (hη : 0 ≤ η)
    (hdebt : ActualRemainingPaperDebt Λ h liouville a I α η) :
    PrefixLittleO (aShift Λ h) ∧ ∃ J : Finset ℤ, QuadraticObstruction liouville J := by
  rcases hdebt with ⟨hforward, hendgame⟩
  refine ⟨?_, ?_⟩
  · exact conditional_fixed_shift_theorem_of_actualRemainingForwardDebt Λ h hforward
  · exact quadratic_obstruction_of_actualRemainingEndgameDebt
      liouville a h I α η hη hendgame

end Pass44ActualDebtInterfaces

end FixedShiftLiouville

/-! ## Pass 45 addendum: weaken the forward core and restate Section 8 in top-mean form -/

namespace FixedShiftLiouville

section Pass45ForwardCore

/--
A universal interval-local form of the Section 7 block estimate.

This removes the dyadic-window and critical-scale bookkeeping from the core analytic statement. What
remains is the finite interval inequality itself: every short block is controlled by the local `U²`
norm of that very interval.
-/
def IntervalLocalU2BlockEstimate (a : ℕ → ℝ) : Prop :=
  ∀ x M : ℕ,
    |B a x M| ≤ (M : ℝ) * localU2Norm (natLift a) (zInterval x M)

/--
The universal interval-local block estimate implies the earlier Section 7 pointwise block control
used throughout the formalization.
-/
theorem localU2BlockControl_of_intervalLocalU2BlockEstimate
    {a : ℕ → ℝ}
    (hcore : IntervalLocalU2BlockEstimate a) :
    LocalU2BlockControl a := by
  intro X M x hM hx
  exact hcore x M

/--
The weakened Section 4 core for the forward argument: the `sup_{1≤L≤H}` oscillation statement
already suffices, without retaining the stronger coefficient-level positive-domination input.
-/
def Section4SupremumCoreHyp (a : ℕ → ℝ) : Prop :=
  DirichletXOscillationSupControl a

/--
The weakened Section 7 core for the forward argument: the true finite inequality is the interval-
local `U²` block estimate, before any restriction to critical scales or dyadic windows.
-/
def Section7FiniteIntervalCoreHyp (a : ℕ → ℝ) : Prop :=
  IntervalLocalU2BlockEstimate a

/--
The weakened Section 4 forward core already implies the eventual critical-scale max interface.
-/
theorem eventualDirichletXOscillationMaxControl_of_section4SupremumCore
    {a : ℕ → ℝ}
    (hsec4 : Section4SupremumCoreHyp a) :
    EventualDirichletXOscillationMaxControl a := by
  exact eventualDirichletXOscillationMaxControl_of_XSup (a := a) hsec4

/--
The weakened Section 7 finite interval core already implies the eventual summed block interface.
-/
theorem eventualLocalU2SummedBlockControl_of_section7FiniteIntervalCore
    {a : ℕ → ℝ}
    (hsec7 : Section7FiniteIntervalCoreHyp a) :
    EventualLocalU2SummedBlockControl a := by
  have hblock : LocalU2BlockControl a :=
    localU2BlockControl_of_intervalLocalU2BlockEstimate (a := a) hsec7
  exact eventualLocalU2SummedBlockControl_of_pointwise (a := a) hblock

/--
Pass 45 forward debt: only the `sup`-form Section 4 statement, the universal finite Section 7
interval inequality, and the averaged local `U²` hypothesis remain.
-/
def Pass45RemainingForwardDebt (a : ℕ → ℝ) : Prop :=
  Section4SupremumCoreHyp a ∧ Section7FiniteIntervalCoreHyp a ∧ LocalU2Hyp a

/--
The pass 45 forward debt already implies the minimal forward interface used by the final reduction
chain.
-/
theorem minimalMainForwardHyp_of_pass45RemainingForwardDebt
    {a : ℕ → ℝ}
    (hdebt : Pass45RemainingForwardDebt a) :
    MinimalMainForwardHyp a := by
  rcases hdebt with ⟨hsec4, hsec7, hU2⟩
  refine ⟨?_, ?_, hU2⟩
  · exact eventualDirichletXOscillationMaxControl_of_section4SupremumCore
      (a := a) hsec4
  · exact eventualLocalU2SummedBlockControl_of_section7FiniteIntervalCore
      (a := a) hsec7

/--
Fixed-shift specialization of the pass 45 forward debt.
-/
theorem conditional_fixed_shift_theorem_of_pass45RemainingForwardDebt
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (hdebt : Pass45RemainingForwardDebt (aShift Λ h)) :
    PrefixLittleO (aShift Λ h) := by
  exact conditional_fixed_shift_theorem_minimal Λ h
    (minimalMainForwardHyp_of_pass45RemainingForwardDebt
      (a := aShift Λ h) hdebt)

end Pass45ForwardCore

end FixedShiftLiouville


namespace FixedShiftLiouville
namespace ProjectedPackets

section Pass45BiasStableResidue

/--
A top-mean version of the pass 43 stable bridge.

This is the Section 8 endgame in the language of the paper's bottleneck remark: after selecting a
small prime with a large projected delta packet, it is enough to upgrade that packet to projected
top bias at some dyadic scale together with the stable-scale rigidity input that turns such bias
into a quadratic obstruction.
-/
def ProjectedDeltaToBiasStableBridge
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ) : Prop :=
  ∀ {p : ℕ}, Nat.Prime p → IntNotDvd p h → p ≤ primeSelectorCutoff I.card →
    (η * (divisibleCount I p : ℝ)) ^ 2 ≤ projectedDeltaPacket a I p α →
      ∃ ρ : ℝ, ∃ a₀ : ℤ, ∃ L : ℕ, 0 < L ∧
        UnitModulus (projectedSignal liouville α h p) ∧
        ProjectedBiasQuadraticBridgeStable
          liouville (projectedSignal liouville α h p) a₀ L ρ

/--
The defect-stable bridge from pass 43 immediately implies the top-mean stable bridge by the exact
projected transport identity.
-/
theorem projectedDeltaToBiasStableBridge_of_defectStable
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ)
    (hbridge : ProjectedDeltaToDefectStableBridge liouville a h I α η) :
    ProjectedDeltaToBiasStableBridge liouville a h I α η := by
  intro p hp hph hcut hpacket
  rcases hbridge (p := p) hp hph hcut hpacket with ⟨δ, a₀, L, hL, hunit, hdef⟩
  refine ⟨1 - δ, a₀, L, hL, hunit, ?_⟩
  exact projectedBiasQuadraticBridgeStable_of_projectedDefect
    liouville (projectedSignal liouville α h p) a₀ L δ hunit hdef

/--
A selector together with the top-mean stable bridge already yields a quadratic obstruction.
-/
theorem small_prime_selector_to_quadratic_obstruction_biasStable
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ)
    (hη : 0 ≤ η)
    (hsel : SmallPrimeSliceBiasSelector a h I α η)
    (hbridge : ProjectedDeltaToBiasStableBridge liouville a h I α η) :
    ∃ J : Finset ℤ, QuadraticObstruction liouville J := by
  rcases small_prime_selector_gives_projected_delta_packet a h I α η hη hsel with
    ⟨p, hp, hph, hcut, hpacket⟩
  rcases hbridge (p := p) hp hph hcut hpacket with ⟨ρ, a₀, L, hL, hunit, hbias⟩
  exact quadratic_obstruction_of_projectedBiasQuadraticBridgeStable
    liouville (projectedSignal liouville α h p) a₀ L ρ hunit hL hbias

/--
The Section 8 bottleneck in explicit top-mean form.

This is the paper-shaped residue after pass 45: a small-prime selector plus a bridge from the
resulting projected delta packet to projected top bias and stable-scale rigidity.
-/
def RemainingBottleneckSelectorBiasStableHyp
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ) : Prop :=
  SmallPrimeSliceBiasSelector a h I α η ∧
  ProjectedDeltaToBiasStableBridge liouville a h I α η

/--
The explicit top-mean residue already forces a quadratic obstruction.
-/
theorem quadratic_obstruction_of_remainingBottleneckSelectorBiasStable
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ)
    (hη : 0 ≤ η)
    (hbottleneck : RemainingBottleneckSelectorBiasStableHyp liouville a h I α η) :
    ∃ J : Finset ℤ, QuadraticObstruction liouville J := by
  rcases hbottleneck with ⟨hsel, hbridge⟩
  exact small_prime_selector_to_quadratic_obstruction_biasStable
    liouville a h I α η hη hsel hbridge

/--
The pass 43 selector/rigidity stable residue implies the pass 45 top-mean stable residue.
-/
theorem remainingBottleneckSelectorBiasStableHyp_of_selectorRigidityStable
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ)
    (hbottleneck : RemainingBottleneckSelectorRigidityStableHyp liouville a h I α η) :
    RemainingBottleneckSelectorBiasStableHyp liouville a h I α η := by
  rcases hbottleneck with ⟨hsel, hbridge⟩
  exact ⟨hsel,
    projectedDeltaToBiasStableBridge_of_defectStable liouville a h I α η hbridge⟩

end Pass45BiasStableResidue

end ProjectedPackets
end FixedShiftLiouville


namespace FixedShiftLiouville

section Pass45ActualDebtInterfaces

/--
Pass 45 endgame core: the Section 8 residue in top-mean form.
-/
def Section8BiasStableCoreHyp
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ) : Prop :=
  ProjectedPackets.RemainingBottleneckSelectorBiasStableHyp liouville a h I α η

/--
Pass 45 endgame debt already forces a quadratic obstruction.
-/
theorem quadratic_obstruction_of_section8BiasStableCore
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ)
    (hη : 0 ≤ η)
    (hcore : Section8BiasStableCoreHyp liouville a h I α η) :
    ∃ J : Finset ℤ, QuadraticObstruction liouville J := by
  exact ProjectedPackets.quadratic_obstruction_of_remainingBottleneckSelectorBiasStable
    liouville a h I α η hη hcore

/--
A pass 45 bundled package for the currently unproved part of the argument.
-/
def Pass45RemainingPaperDebt
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (liouville a : ℤ → ℂ) (I : Finset ℤ) (α η : ℝ) : Prop :=
  Pass45RemainingForwardDebt (aShift Λ h) ∧
  Section8BiasStableCoreHyp liouville a h I α η

/--
Consequences of the pass 45 remaining paper debt package.
-/
theorem consequences_of_pass45RemainingPaperDebt
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (liouville a : ℤ → ℂ) (I : Finset ℤ) (α η : ℝ)
    (hη : 0 ≤ η)
    (hdebt : Pass45RemainingPaperDebt Λ h liouville a I α η) :
    PrefixLittleO (aShift Λ h) ∧ ∃ J : Finset ℤ, QuadraticObstruction liouville J := by
  rcases hdebt with ⟨hforward, hendgame⟩
  refine ⟨?_, ?_⟩
  · exact conditional_fixed_shift_theorem_of_pass45RemainingForwardDebt Λ h hforward
  · exact quadratic_obstruction_of_section8BiasStableCore
      liouville a h I α η hη hendgame

end Pass45ActualDebtInterfaces

end FixedShiftLiouville


/-! ## Pass 46 addendum: exact square-one forward core and single-prime top-mean endgame -/

namespace FixedShiftLiouville

section Pass46ForwardCore

/--
The exact Section 4 square-one main-term statement already equivalent to the pass 45 supremum core.
This is the finite paper-shaped formulation `|dirichletMainTerm a X H - X| ≤ C * (...)` on the
square-one window, stripped of the extra supremum wrapper.
-/
def Section4SquareOneMainTermCoreHyp (a : ℕ → ℝ) : Prop :=
  DirichletXMainTermControlOnSquareOne a

/--
The pass 46 square-one Section 4 core implies the pass 45 supremum core.
-/
theorem section4SupremumCoreHyp_of_squareOneMainTermCore
    {a : ℕ → ℝ}
    (hcore : Section4SquareOneMainTermCoreHyp a) :
    Section4SupremumCoreHyp a := by
  exact (dirichletXOscillationSupControl_iff_XMainTermControlOnSquareOne (a := a)).mpr hcore

/--
Conversely, the pass 45 supremum core is exactly the pass 46 square-one main-term control.
-/
theorem squareOneMainTermCoreHyp_of_section4SupremumCore
    {a : ℕ → ℝ}
    (hcore : Section4SupremumCoreHyp a) :
    Section4SquareOneMainTermCoreHyp a := by
  exact (dirichletXOscillationSupControl_iff_XMainTermControlOnSquareOne (a := a)).mp hcore

/--
The exact square-one Section 4 core already implies the current eventual critical-scale max
interface.
-/
theorem eventualDirichletXOscillationMaxControl_of_section4SquareOneMainTermCore
    {a : ℕ → ℝ}
    (hcore : Section4SquareOneMainTermCoreHyp a) :
    EventualDirichletXOscillationMaxControl a := by
  exact eventualDirichletXOscillationMaxControl_of_XMainTermControlOnSquareOne
    (a := a) hcore

/--
Pass 46 forward debt: the exact square-one Section 4 theorem, the finite interval Section 7 block
estimate, and the averaged local `U²` input.
-/
def Pass46RemainingForwardDebt (a : ℕ → ℝ) : Prop :=
  Section4SquareOneMainTermCoreHyp a ∧ Section7FiniteIntervalCoreHyp a ∧ LocalU2Hyp a

/--
Pass 46 forward debt implies the pass 45 forward debt.
-/
theorem pass45RemainingForwardDebt_of_pass46
    {a : ℕ → ℝ}
    (hdebt : Pass46RemainingForwardDebt a) :
    Pass45RemainingForwardDebt a := by
  rcases hdebt with ⟨hsec4, hsec7, hU2⟩
  exact ⟨section4SupremumCoreHyp_of_squareOneMainTermCore (a := a) hsec4, hsec7, hU2⟩

/--
Hence the pass 46 forward debt already gives the fixed-shift conclusion.
-/
theorem conditional_fixed_shift_theorem_of_pass46RemainingForwardDebt
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (hdebt : Pass46RemainingForwardDebt (aShift Λ h)) :
    PrefixLittleO (aShift Λ h) := by
  exact conditional_fixed_shift_theorem_of_pass45RemainingForwardDebt Λ h
    (pass45RemainingForwardDebt_of_pass46 (a := aShift Λ h) hdebt)

end Pass46ForwardCore

end FixedShiftLiouville


namespace FixedShiftLiouville
namespace ProjectedPackets

section Pass46SinglePrimeBiasStable

/--
A single-prime top-mean stable witness.

This is the exact Section 8 endpoint after performing the selector step: one prime survives, together
with the slice bias needed to justify that choice, and at that same prime one has a projected
top-mean witness plus stable-scale rigidity.
-/
def SelectedPrimeBiasStableWitness
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ) : Prop :=
  ∃ p : ℕ, Nat.Prime p ∧ IntNotDvd p h ∧ p ≤ primeSelectorCutoff I.card ∧
    η * (divisibleCount I p : ℝ) ≤ ‖divisibleSliceSum a I p α‖ ∧
    ∃ ρ : ℝ, ∃ a₀ : ℤ, ∃ L : ℕ, 0 < L ∧
      UnitModulus (projectedSignal liouville α h p) ∧
      ProjectedBiasQuadraticBridgeStable
        liouville (projectedSignal liouville α h p) a₀ L ρ

/--
The pass 45 selector-plus-uniform-bridge residue collapses to a single chosen prime with the
required top-mean stable witness.
-/
theorem selectedPrimeBiasStableWitness_of_selectorBiasStable
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ)
    (hη : 0 ≤ η)
    (hbottleneck : RemainingBottleneckSelectorBiasStableHyp liouville a h I α η) :
    SelectedPrimeBiasStableWitness liouville a h I α η := by
  rcases hbottleneck with ⟨hsel, hbridge⟩
  rcases hsel with ⟨p, hp, hph, hcut, hslice⟩
  have hpacket :
      (η * (divisibleCount I p : ℝ)) ^ 2 ≤ projectedDeltaPacket a I p α := by
    exact projected_delta_packet_large_of_slice_bias a I p α η hη hslice
  rcases hbridge (p := p) hp hph hcut hpacket with ⟨ρ, a₀, L, hL, hunit, hbias⟩
  exact ⟨p, hp, hph, hcut, hslice, ρ, a₀, L, hL, hunit, hbias⟩

/--
The earlier selected-prime defect-stable witness upgrades to the new top-mean stable witness via
the exact transport identity.
-/
theorem selectedPrimeBiasStableWitness_of_selectedPrimeDefectStableWitness
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ)
    (hwitness : SelectedPrimeDefectStableWitness liouville a h I α η) :
    SelectedPrimeBiasStableWitness liouville a h I α η := by
  rcases hwitness with ⟨p, hp, hph, hcut, hslice, δ, a₀, L, hL, hunit, hdef⟩
  refine ⟨p, hp, hph, hcut, hslice, 1 - δ, a₀, L, hL, hunit, ?_⟩
  exact projectedBiasQuadraticBridgeStable_of_projectedDefect
    liouville (projectedSignal liouville α h p) a₀ L δ hunit hdef

/--
A single chosen prime with projected top bias and stable-scale rigidity already forces a quadratic
obstruction.
-/
theorem quadratic_obstruction_of_selectedPrimeBiasStableWitness
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ)
    (hwitness : SelectedPrimeBiasStableWitness liouville a h I α η) :
    ∃ J : Finset ℤ, QuadraticObstruction liouville J := by
  rcases hwitness with ⟨p, hp, hph, hcut, hslice, ρ, a₀, L, hL, hunit, hbias⟩
  exact quadratic_obstruction_of_projectedBiasQuadraticBridgeStable
    liouville (projectedSignal liouville α h p) a₀ L ρ hunit hL hbias

/--
The pass 45 top-mean bottleneck implies the single-prime pass 46 witness.
-/
theorem selectedPrimeBiasStableWitness_of_remainingBottleneckSelectorBiasStable
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ)
    (hη : 0 ≤ η)
    (hbottleneck : RemainingBottleneckSelectorBiasStableHyp liouville a h I α η) :
    SelectedPrimeBiasStableWitness liouville a h I α η := by
  exact selectedPrimeBiasStableWitness_of_selectorBiasStable
    liouville a h I α η hη hbottleneck

/--
The older existential selected-prime defect witness also implies the pass 46 single-prime top-mean
stable witness.
-/
theorem selectedPrimeBiasStableWitness_of_remainingBottleneckSelectedPrimeStable
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ)
    (hbottleneck : RemainingBottleneckSelectedPrimeStableHyp liouville a h I α η) :
    SelectedPrimeBiasStableWitness liouville a h I α η := by
  exact selectedPrimeBiasStableWitness_of_selectedPrimeDefectStableWitness
    liouville a h I α η hbottleneck

end Pass46SinglePrimeBiasStable

end ProjectedPackets
end FixedShiftLiouville


namespace FixedShiftLiouville

section Pass46ActualDebtInterfaces

/--
Pass 46 Section 8 core: a single selected prime carrying the final top-mean/stable witness.
-/
def Section8SinglePrimeBiasStableCoreHyp
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ) : Prop :=
  ProjectedPackets.SelectedPrimeBiasStableWitness liouville a h I α η

/--
The single-prime pass 46 Section 8 core already yields a quadratic obstruction.
-/
theorem quadratic_obstruction_of_section8SinglePrimeBiasStableCore
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ)
    (hcore : Section8SinglePrimeBiasStableCoreHyp liouville a h I α η) :
    ∃ J : Finset ℤ, QuadraticObstruction liouville J := by
  exact ProjectedPackets.quadratic_obstruction_of_selectedPrimeBiasStableWitness
    liouville a h I α η hcore

/--
The pass 45 Section 8 core implies the pass 46 single-prime Section 8 core.
-/
theorem section8SinglePrimeBiasStableCoreHyp_of_section8BiasStableCore
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ)
    (hη : 0 ≤ η)
    (hcore : Section8BiasStableCoreHyp liouville a h I α η) :
    Section8SinglePrimeBiasStableCoreHyp liouville a h I α η := by
  exact ProjectedPackets.selectedPrimeBiasStableWitness_of_remainingBottleneckSelectorBiasStable
    liouville a h I α η hη hcore

/--
The older pass 42/43 minimal selected-prime stable bottleneck also implies the pass 46 single-prime
top-mean stable core.
-/
theorem section8SinglePrimeBiasStableCoreHyp_of_minimalSection8EndgameHyp
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ)
    (hcore : MinimalSection8EndgameHyp liouville a h I α η) :
    Section8SinglePrimeBiasStableCoreHyp liouville a h I α η := by
  exact ProjectedPackets.selectedPrimeBiasStableWitness_of_remainingBottleneckSelectedPrimeStable
    liouville a h I α η hcore

/--
Pass 46 bundled paper debt:
the exact square-one Section 4 theorem, the finite interval Section 7 inequality, and one selected
prime carrying the final top-mean/stable Section 8 witness.
-/
def Pass46RemainingPaperDebt
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (liouville a : ℤ → ℂ) (I : Finset ℤ) (α η : ℝ) : Prop :=
  Pass46RemainingForwardDebt (aShift Λ h) ∧
  Section8SinglePrimeBiasStableCoreHyp liouville a h I α η

/--
Consequences of the pass 46 remaining paper debt package.
-/
theorem consequences_of_pass46RemainingPaperDebt
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (liouville a : ℤ → ℂ) (I : Finset ℤ) (α η : ℝ) :
    Pass46RemainingPaperDebt Λ h liouville a I α η →
    PrefixLittleO (aShift Λ h) ∧ ∃ J : Finset ℤ, QuadraticObstruction liouville J := by
  intro hdebt
  rcases hdebt with ⟨hforward, hendgame⟩
  refine ⟨?_, ?_⟩
  · exact conditional_fixed_shift_theorem_of_pass46RemainingForwardDebt Λ h hforward
  · exact quadratic_obstruction_of_section8SinglePrimeBiasStableCore
      liouville a h I α η hendgame

end Pass46ActualDebtInterfaces

end FixedShiftLiouville


namespace FixedShiftLiouville

section LocalU2FourthPowerBridge

open Complex

/-- Reindex a shifted integer interval inside the local correlation sum. -/
theorem sum_shift_zInterval
    (f : ℤ → ℂ) (x M : ℕ) {n : ℤ}
    (hn : n ∈ zInterval (x : ℤ) M) :
    ∑ t ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
      (if n + t ∈ zInterval (x : ℤ) M then f (n + t) else 0)
      = ∑ m ∈ zInterval (x : ℤ) M, f m := by
  classical
  let S := (Finset.Icc (-(M : ℤ)) (M : ℤ)).filter
    (fun t : ℤ => n + t ∈ zInterval (x : ℤ) M)
  have hfilter :
      (∑ t ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
        (if n + t ∈ zInterval (x : ℤ) M then f (n + t) else 0))
        = ∑ t ∈ S, f (n + t) := by
    simp [S, Finset.sum_filter]
  rw [hfilter]
  refine Finset.sum_nbij' (s := S) (t := zInterval (x : ℤ) M)
    (fun t => n + t) (fun m => m - n) ?hi ?hj ?left ?right ?hfg
  · intro t ht
    exact (Finset.mem_filter.mp ht).2
  · intro m hm
    have hn' : n ∈ Finset.Icc ((x : ℤ) + 1) ((x : ℤ) + M) := by simpa [zInterval] using hn
    have hm' : m ∈ Finset.Icc ((x : ℤ) + 1) ((x : ℤ) + M) := by simpa [zInterval] using hm
    have hnI := Finset.mem_Icc.mp hn'
    have hmI := Finset.mem_Icc.mp hm'
    refine Finset.mem_filter.mpr ?_
    constructor
    · refine Finset.mem_Icc.mpr ?_
      constructor
      · change -((M : ℤ)) ≤ m - n
        omega
      · change m - n ≤ (M : ℤ)
        omega
    · have hnm : n + (m - n) = m := by ring
      simpa [hnm] using hm
  · intro t ht
    ring
  · intro m hm
    ring
  · intro t ht
    rfl

/-- Summing all local correlations over the admissible shifts recovers `S_I * conj S_I`. -/
theorem sum_localU2Correlation_zInterval_complex
    (f : ℤ → ℂ) (x M : ℕ) :
    ∑ t ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
      localU2Correlation f (zInterval (x : ℤ) M) t
      = (∑ n ∈ zInterval (x : ℤ) M, f n) *
          star (∑ n ∈ zInterval (x : ℤ) M, f n) := by
  classical
  unfold localU2Correlation
  calc
    ∑ t ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
        ∑ n ∈ zInterval (x : ℤ) M,
          (if n + t ∈ zInterval (x : ℤ) M then f (n + t) * star (f n) else 0)
        = ∑ n ∈ zInterval (x : ℤ) M,
            ∑ t ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
              (if n + t ∈ zInterval (x : ℤ) M then f (n + t) * star (f n) else 0) := by
          rw [Finset.sum_comm]
    _ = ∑ n ∈ zInterval (x : ℤ) M,
            (∑ m ∈ zInterval (x : ℤ) M, f m) * star (f n) := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          have hshift := sum_shift_zInterval (fun m => f m * star (f n)) x M hn
          calc
            ∑ t ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
              (if n + t ∈ zInterval (x : ℤ) M then f (n + t) * star (f n) else 0)
                = ∑ m ∈ zInterval (x : ℤ) M, f m * star (f n) := hshift
            _ = (∑ m ∈ zInterval (x : ℤ) M, f m) * star (f n) := by
                  rw [← Finset.sum_mul]
    _ = (∑ m ∈ zInterval (x : ℤ) M, f m) *
          (∑ n ∈ zInterval (x : ℤ) M, star (f n)) := by
          rw [← Finset.mul_sum]
    _ = (∑ n ∈ zInterval (x : ℤ) M, f n) *
          star (∑ n ∈ zInterval (x : ℤ) M, f n) := by
          simp [map_sum, mul_assoc, mul_comm, mul_left_comm]

/-- The lifted natural block sum agrees with the integer-block sum. -/
theorem sum_natLift_zInterval_eq_B
    (a : ℕ → ℝ) (x M : ℕ) :
    ∑ n ∈ zInterval (x : ℤ) M, natLift a n = (B a x M : ℂ) := by
  classical
  unfold B
  rw [Complex.ofReal_sum]
  refine Finset.sum_nbij' (s := zInterval (x : ℤ) M) (t := Finset.Icc (x + 1) (x + M))
    (fun n => n.toNat) (fun m => (m : ℤ)) ?hi ?hj ?left ?right ?hfg
  · intro n hn
    have hn' : n ∈ Finset.Icc ((x : ℤ) + 1) ((x : ℤ) + M) := by simpa [zInterval] using hn
    have hnI := Finset.mem_Icc.mp hn'
    have hn_nonneg : 0 ≤ n := by omega
    have hto : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg hn_nonneg
    refine Finset.mem_Icc.mpr ?_
    constructor
    · exact_mod_cast (by simpa [hto] using hnI.1)
    · exact_mod_cast (by simpa [hto] using hnI.2)
  · intro m hm
    have hmI := Finset.mem_Icc.mp hm
    refine Finset.mem_Icc.mpr ?_
    constructor
    · simpa using (show ((x + 1 : ℕ) : ℤ) ≤ (m : ℤ) by exact_mod_cast hmI.1)
    · simpa using (show (m : ℤ) ≤ ((x + M : ℕ) : ℤ) by exact_mod_cast hmI.2)
  · intro n hn
    have hn' : n ∈ Finset.Icc ((x : ℤ) + 1) ((x : ℤ) + M) := by simpa [zInterval] using hn
    have hnI := Finset.mem_Icc.mp hn'
    exact Int.toNat_of_nonneg (by omega)
  · intro m hm
    simp
  · intro n hn
    have hn_nonneg : 0 ≤ n := by
      have hnI := Finset.mem_Icc.mp hn
      omega
    simp [natLift, hn_nonneg]

/-- On the integer interval `[x+1,x+M]`, summing the local additive correlations over all
admissible shifts exactly recovers the squared block sum. -/
theorem sum_localU2Correlation_zInterval_eq_block_normSq
    (a : ℕ → ℝ) (x M : ℕ) :
    ∑ t ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
      localU2Correlation (natLift a) (zInterval (x : ℤ) M) t
      = ((B a x M : ℂ) * star (B a x M : ℂ)) := by
  rw [sum_localU2Correlation_zInterval_complex]
  rw [sum_natLift_zInterval_eq_B]

/-- Cauchy--Schwarz on the correlation expansion gives the basic fourth-power estimate. -/
theorem block_fourth_le_three_mul_u2Fourth
    (a : ℕ → ℝ) (x M : ℕ) (hM : 1 ≤ M) :
    |B a x M| ^ 4
      ≤ (3 : ℝ) * (M : ℝ) * localU2Fourth (natLift a) (zInterval (x : ℤ) M) := by
  classical
  let s := Finset.Icc (-(M : ℤ)) (M : ℤ)
  let C : ℤ → ℂ := fun t => localU2Correlation (natLift a) (zInterval (x : ℤ) M) t
  have hsum := sum_localU2Correlation_zInterval_eq_block_normSq (a := a) (x := x) (M := M)
  have hnorm_sum : ‖∑ t ∈ s, C t‖ ^ 2 ≤ (s.card : ℝ) * ∑ t ∈ s, ‖C t‖ ^ 2 := by
    have htri : ‖∑ t ∈ s, C t‖ ≤ ∑ t ∈ s, ‖C t‖ := norm_sum_le _ _
    have htri_sq : ‖∑ t ∈ s, C t‖ ^ 2 ≤ (∑ t ∈ s, ‖C t‖) ^ 2 := by
      exact pow_le_pow_left₀ (norm_nonneg _) htri 2
    exact le_trans htri_sq (sq_sum_le_card_mul_sum_sq :
      (∑ t ∈ s, ‖C t‖) ^ 2 ≤ (s.card : ℝ) * ∑ t ∈ s, ‖C t‖ ^ 2)
  have hcard : (s.card : ℝ) ≤ 3 * (M : ℝ) := by
    have hcardNat : s.card = (2 * M + 1) := by
      dsimp [s]
      rw [Int.card_Icc]
      change Int.toNat ((M : ℤ) + 1 - -(M : ℤ)) = 2 * M + 1
      rw [show ((M : ℤ) + 1 - -(M : ℤ)) = (2 * M + 1 : ℤ) by ring]
      apply Nat.cast_injective (R := ℤ)
      rw [Int.toNat_of_nonneg]
      · norm_num
      · omega
    rw [hcardNat]
    exact_mod_cast (by omega : 2 * M + 1 ≤ 3 * M)
  have hfourth_eq : |B a x M| ^ 4 = ‖∑ t ∈ s, C t‖ ^ 2 := by
    have hsum' : ∑ t ∈ s, C t = ((B a x M : ℂ) * star (B a x M : ℂ)) := by
      simpa [s, C] using hsum
    rw [hsum']
    simp [Complex.normSq_eq_norm_sq, Complex.normSq_ofReal, normSq, sq_abs]
    have hs : |B a x M| ^ 2 = (B a x M) ^ 2 := sq_abs (B a x M)
    nlinarith [hs]
  have hsq_to_normSq : ∑ t ∈ s, ‖C t‖ ^ 2 = localU2Fourth (natLift a) (zInterval (x : ℤ) M) := by
    have hcardI : (zInterval (x : ℤ) M).card = M := zInterval_card_nat x M
    unfold localU2Fourth
    rw [hcardI]
    simp [s, C, Complex.normSq_eq_norm_sq]
  calc
    |B a x M| ^ 4 = ‖∑ t ∈ s, C t‖ ^ 2 := hfourth_eq
    _ ≤ (s.card : ℝ) * ∑ t ∈ s, ‖C t‖ ^ 2 := hnorm_sum
    _ = (s.card : ℝ) * localU2Fourth (natLift a) (zInterval (x : ℤ) M) := by rw [hsq_to_normSq]
    _ ≤ (3 : ℝ) * (M : ℝ) * localU2Fourth (natLift a) (zInterval (x : ℤ) M) := by
      have hu2_nonneg : 0 ≤ localU2Fourth (natLift a) (zInterval (x : ℤ) M) := by
        unfold localU2Fourth
        exact Finset.sum_nonneg (by
          intro t ht
          exact Complex.normSq_nonneg _)
      exact mul_le_mul_of_nonneg_right hcard hu2_nonneg

/-- The correct finite Section 7 core is a fourth-power estimate, not a linear estimate in the
fourth-power-normalized local `U²` quantity. -/
def IntervalLocalU2FourthPowerEstimate (a : ℕ → ℝ) : Prop :=
  ∀ x M : ℕ, 1 ≤ M →
    |B a x M| ^ 4
      ≤ (3 : ℝ) * (M : ℝ)^4 * localU2Norm (natLift a) (zInterval (x : ℤ) M)

/-- The finite fourth-power estimate follows from the correlation expansion and the normalizer. -/
theorem intervalLocalU2FourthPowerEstimate_unconditional
    (a : ℕ → ℝ) :
    IntervalLocalU2FourthPowerEstimate a := by
  intro x M hM
  have hfourth := block_fourth_le_three_mul_u2Fourth (a := a) (x := x) (M := M) hM
  have hnormer := localU2Normalizer_zInterval_nat x M hM
  unfold localU2Norm
  rw [hnormer]
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (lt_of_lt_of_le (Nat.zero_lt_one) hM)
  have hM3pos : (0 : ℝ) < (M : ℝ)^3 := by positivity
  rw [div_eq_mul_inv]
  calc
    |B a x M| ^ 4 ≤ (3 : ℝ) * (M : ℝ) * localU2Fourth (natLift a) (zInterval (x : ℤ) M) := hfourth
    _ = (3 : ℝ) * (M : ℝ)^4 * (localU2Fourth (natLift a) (zInterval (x : ℤ) M) * ((M : ℝ)^3)⁻¹) := by
      field_simp [ne_of_gt hM3pos]

/-- A scalar Young inequality in the form needed to consume fourth-power local `U²` estimates. -/
theorem young_fourth_scaled
    {y q η M : ℝ}
    (hy : 0 ≤ y) (hM : 0 < M) (hη : 0 < η)
    (hpow : y ^ 4 ≤ (3 : ℝ) * M ^ 4 * q) :
    y ≤ η * M + ((3 : ℝ) / η ^ 3) * M * q := by
  have hM4pos : 0 < M ^ 4 := by positivity
  have ht_nonneg : 0 ≤ y / M := div_nonneg hy hM.le
  have ht_pow : (y / M) ^ 4 ≤ (3 : ℝ) * q := by
    rw [div_pow]
    rw [div_le_iff₀ hM4pos]
    calc
      y ^ 4 ≤ (3 : ℝ) * M ^ 4 * q := hpow
      _ = (3 : ℝ) * q * M ^ 4 := by ring
  have hyoung : y / M ≤ η + ((3 : ℝ) / η ^ 3) * q := by
    by_cases hle : y / M ≤ η
    · have hnonneg : 0 ≤ ((3 : ℝ) / η ^ 3) * q := by
        have h3q : 0 ≤ (3 : ℝ) * q := le_trans (pow_nonneg ht_nonneg 4) ht_pow
        have hη3pos : 0 < η ^ 3 := by positivity
        have hdiv : 0 ≤ ((3 : ℝ) * q) / η ^ 3 := div_nonneg h3q hη3pos.le
        convert hdiv using 1
        ring
      nlinarith
    · have hηle : η ≤ y / M := le_of_not_ge hle
      have hη3pos : 0 < η ^ 3 := by positivity
      have hmain : y / M ≤ ((y / M) ^ 4) / η ^ 3 := by
        rw [le_div_iff₀ hη3pos]
        have hpow3 : η ^ 3 ≤ (y / M) ^ 3 := by gcongr
        nlinarith [mul_le_mul_of_nonneg_left hpow3 ht_nonneg]
      have hmain2 : ((y / M) ^ 4) / η ^ 3 ≤ ((3 : ℝ) * q) / η ^ 3 := by
        exact div_le_div_of_nonneg_right ht_pow hη3pos.le
      have hnonneg_eta : 0 ≤ η := hη.le
      calc
        y / M ≤ ((y / M) ^ 4) / η ^ 3 := hmain
        _ ≤ ((3 : ℝ) * q) / η ^ 3 := hmain2
        _ = ((3 : ℝ) / η ^ 3) * q := by ring
        _ ≤ η + ((3 : ℝ) / η ^ 3) * q := by linarith
  have hmul := mul_le_mul_of_nonneg_right hyoung hM.le
  have hy_eq : y / M * M = y := div_mul_cancel₀ y hM.ne'
  calc
    y = y / M * M := by rw [hy_eq]
    _ ≤ (η + ((3 : ℝ) / η ^ 3) * q) * M := hmul
    _ = η * M + ((3 : ℝ) / η ^ 3) * M * q := by ring

/-- Number of starting points in the short-block window. -/
theorem card_shortBlockWindow_le_X {X M : ℕ}
    (hXpos : 1 ≤ X) (hMpos : 1 ≤ M) :
    ((Finset.Icc X (2 * X - M)).card : ℝ) ≤ X := by
  rw [Nat.card_Icc]
  exact_mod_cast (by omega : 2 * X - M + 1 - X ≤ X)

/-- The fourth-power local `U²` bridge and averaged local `U²` hypothesis imply first moments.
This is the formal fourth-root/Hölder step, implemented through Young's inequality to avoid
`rpow` bookkeeping. -/
theorem firstMoment_of_localU2FourthPower
    {a : ℕ → ℝ}
    (hpow : IntervalLocalU2FourthPowerEstimate a)
    (hU2 : LocalU2Hyp a) :
    FirstMomentHyp a := by
  intro ε hε
  let η : ℝ := ε / 2
  have hη : 0 < η := by dsimp [η]; positivity
  let K : ℝ := (3 : ℝ) / η ^ 3
  have hKpos : 0 < K := by dsimp [K]; positivity
  have hδpos : 0 < ε / (2 * K) := by positivity
  rcases hU2 (ε / (2 * K)) hδpos with ⟨X₀, hX₀⟩
  refine ⟨max X₀ 1, ?_⟩
  intro X M hX hM
  have hX₀le : X₀ ≤ X := le_trans (le_max_left _ _) hX
  have hMpos : 1 ≤ M := (Finset.mem_Icc.mp hM).1
  have hXpos : 1 ≤ X := le_trans (le_max_right _ _) hX
  have hMposR : (0 : ℝ) < M := by exact_mod_cast (lt_of_lt_of_le (Nat.zero_lt_one) hMpos)
  have hpoint : ∀ x ∈ Finset.Icc X (2 * X - M),
      |B a x M| ≤ η * (M : ℝ) + K * (M : ℝ) * localU2Norm (natLift a) (zInterval (x : ℤ) M) := by
    intro x hx
    exact young_fourth_scaled (y := |B a x M|) (q := localU2Norm (natLift a) (zInterval (x : ℤ) M))
      (M := (M : ℝ)) (η := η) (abs_nonneg _) hMposR hη (hpow x M hMpos)
  have hcard : ((Finset.Icc X (2 * X - M)).card : ℝ) ≤ X := card_shortBlockWindow_le_X hXpos hMpos
  calc
    ∑ x ∈ Finset.Icc X (2 * X - M), |B a x M|
        ≤ ∑ x ∈ Finset.Icc X (2 * X - M),
            (η * (M : ℝ) + K * (M : ℝ) * localU2Norm (natLift a) (zInterval (x : ℤ) M)) := by
          refine Finset.sum_le_sum ?_
          intro x hx
          exact hpoint x hx
    _ = ((Finset.Icc X (2 * X - M)).card : ℝ) * (η * (M : ℝ))
          + K * (M : ℝ) * ∑ x ∈ Finset.Icc X (2 * X - M),
              localU2Norm (natLift a) (zInterval (x : ℤ) M) := by
          simp [Finset.sum_add_distrib, mul_sum, sum_mul, mul_assoc, mul_comm, mul_left_comm]
    _ ≤ X * (η * (M : ℝ)) + K * (M : ℝ) * (ε / (2 * K) * X) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_right hcard (mul_nonneg hη.le (by positivity))
          · exact mul_le_mul_of_nonneg_left (hX₀ hX₀le hM) (mul_nonneg hKpos.le (by positivity))
    _ = ε * X * M := by
          dsimp [η, K]
          field_simp [ne_of_gt hKpos]
          ring

end LocalU2FourthPowerBridge

end FixedShiftLiouville

/-! ## Pass 47 addendum: Section 7 with the paper's corrected fourth-power bridge -/

namespace FixedShiftLiouville

section Pass47LocalU2Constants

/--
A constant-sensitive version of the Section 7 block estimate.

This matches the statement in the paper: block sums are controlled by the local `U²` norm up to an
absolute multiplicative constant, rather than with coefficient exactly `1`.
-/
def LocalU2BlockControlWithConst (a : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ ⦃X M x : ℕ⦄,
    M ∈ Finset.Icc 1 (criticalScale X) →
    x ∈ Finset.Icc X (2 * X - M) →
      |B a x M| ≤ (C * (M : ℝ)) * localU2Norm (natLift a) (zInterval x M)

/--
The older exact-coefficient pointwise block estimate implies the constant-sensitive one with
constant `1`.
-/
theorem localU2BlockControlWithConst_of_exact
    {a : ℕ → ℝ}
    (hblock : LocalU2BlockControl a) :
    LocalU2BlockControlWithConst a := by
  refine ⟨1, by positivity, ?_⟩
  intro X M x hM hx
  simpa [one_mul] using hblock hM hx

/--
A universal interval-local version of the constant-sensitive Section 7 block estimate.
-/
def IntervalLocalU2BlockEstimateWithConst (a : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ x M : ℕ,
    |B a x M| ≤ (C * (M : ℝ)) * localU2Norm (natLift a) (zInterval x M)

/--
The universal interval-local constant-sensitive estimate implies the dyadic-window version used in
Section 7.
-/
theorem localU2BlockControlWithConst_of_intervalLocalU2BlockEstimateWithConst
    {a : ℕ → ℝ}
    (hcore : IntervalLocalU2BlockEstimateWithConst a) :
    LocalU2BlockControlWithConst a := by
  rcases hcore with ⟨C, hC, hcoreC⟩
  refine ⟨C, hC, ?_⟩
  intro X M x hM hx
  exact hcoreC x M

/--
The exact-coefficient interval-local bound implies the constant-sensitive version with constant `1`.
-/
theorem intervalLocalU2BlockEstimateWithConst_of_exact
    {a : ℕ → ℝ}
    (hcore : IntervalLocalU2BlockEstimate a) :
    IntervalLocalU2BlockEstimateWithConst a := by
  refine ⟨1, by positivity, ?_⟩
  intro x M
  simpa [one_mul] using hcore x M

/--
A constant-sensitive Section 7 block estimate still upgrades the averaged local `U²` hypothesis to
a first-moment bound.
-/
theorem firstMoment_of_localU2WithConst
    {a : ℕ → ℝ}
    (hblock : LocalU2BlockControlWithConst a)
    (hU2 : LocalU2Hyp a) :
    FirstMomentHyp a := by
  rcases hblock with ⟨C, hC, hblockC⟩
  intro ε hε
  have hCp1 : 0 < C + 1 := by
    nlinarith
  have hδpos : 0 < ε / (C + 1) := by
    exact div_pos hε hCp1
  rcases hU2 (ε / (C + 1)) hδpos with ⟨X₀, hX₀⟩
  refine ⟨X₀, ?_⟩
  intro X M hX hM
  have hpoint :
      ∀ x ∈ Finset.Icc X (2 * X - M),
        |B a x M| ≤ (C * (M : ℝ)) * localU2Norm (natLift a) (zInterval x M) := by
    intro x hx
    exact hblockC hM hx
  have hsumU2 :
      ∑ x ∈ Finset.Icc X (2 * X - M), localU2Norm (natLift a) (zInterval x M)
        ≤ (ε / (C + 1)) * X := by
    exact hX₀ hX hM
  have hcoeff_nonneg : 0 ≤ C * (M : ℝ) := by
    exact mul_nonneg hC (Nat.cast_nonneg M)
  calc
    ∑ x ∈ Finset.Icc X (2 * X - M), |B a x M|
        ≤ ∑ x ∈ Finset.Icc X (2 * X - M),
            (C * (M : ℝ)) * localU2Norm (natLift a) (zInterval x M) := by
              refine Finset.sum_le_sum ?_
              intro x hx
              exact hpoint x hx
    _ = (C * (M : ℝ)) * ∑ x ∈ Finset.Icc X (2 * X - M),
            localU2Norm (natLift a) (zInterval x M) := by
          rw [mul_sum]
    _ ≤ (C * (M : ℝ)) * ((ε / (C + 1)) * X) := by
          exact mul_le_mul_of_nonneg_left hsumU2 hcoeff_nonneg
    _ ≤ ε * X * M := by
          have hMnonneg : 0 ≤ (M : ℝ) := by positivity
          have hXnonneg : 0 ≤ (X : ℝ) := by positivity
          have hεnonneg : 0 ≤ ε := le_of_lt hε
          have hCp1pos : 0 < C + 1 := by nlinarith
          have hcoef : C * (ε / (C + 1)) ≤ ε := by
            have hfrac : C / (C + 1) ≤ 1 := by
              rw [div_le_one hCp1pos]
              nlinarith
            calc
              C * (ε / (C + 1)) = ε * (C / (C + 1)) := by ring
              _ ≤ ε * 1 := by exact mul_le_mul_of_nonneg_left hfrac hεnonneg
              _ = ε := by ring
          have hstep : (C * (M : ℝ)) * ((ε / (C + 1)) * X) ≤ ε * X * M := by
            nlinarith [mul_le_mul_of_nonneg_right hcoef hXnonneg]
          exact hstep

/--
The cleaned Section 6 theorem still follows from the square-one Section 4 bridge together with the
constant-sensitive Section 7 estimate.
-/
theorem uniform_local_U2_criterion_squareOneMainTerm_withConst
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    (hsqev : EventuallySquareOne a)
    (hctrl : DirichletMainTermControlOnSquareOne a)
    (hblock : LocalU2BlockControlWithConst a)
    (hU2 : LocalU2Hyp a) :
    PrefixLittleO a := by
  have hfirst : FirstMomentHyp a := firstMoment_of_localU2WithConst hblock hU2
  exact short_interval_first_moment_theorem_squareOneMainTerm ha hsqev hctrl hfirst

/--
Fixed-shift specialization of the constant-sensitive Section 7 route.
-/
theorem conditional_fixed_shift_theorem_localU2_squareOneMainTerm_withConst
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (hctrl : DirichletMainTermControlOnSquareOne (aShift Λ h))
    (hblock : LocalU2BlockControlWithConst (aShift Λ h))
    (hU2 : LocalU2Hyp (aShift Λ h)) :
    PrefixLittleO (aShift Λ h) := by
  have hbound : BoundedByOne (aShift Λ h) := aShift_boundedByOne Λ h
  have hsqev : EventuallySquareOne (aShift Λ h) := aShift_eventuallySquareOne Λ h
  exact uniform_local_U2_criterion_squareOneMainTerm_withConst
    (a := aShift Λ h) hbound hsqev hctrl hblock hU2

/--
The paper-faithful Section 7 core in pass 47: the corrected interval-local fourth-power estimate.
-/
def Section7FiniteIntervalCoreHypWithConst (a : ℕ → ℝ) : Prop :=
  IntervalLocalU2FourthPowerEstimate a

/--
The pass 46 exact interval-local Section 7 core implies the paper-faithful constant-sensitive pass
47 core.
-/
theorem section7FiniteIntervalCoreHypWithConst_of_pass46
    {a : ℕ → ℝ}
    (hcore : Section7FiniteIntervalCoreHyp a) :
    Section7FiniteIntervalCoreHypWithConst a := by
  exact intervalLocalU2FourthPowerEstimate_unconditional a

/--
Pass 47 forward debt: the exact square-one Section 4 theorem, the paper-faithful Section 7 block
estimate with an absolute constant, and the averaged local `U²` input.
-/
def Pass47RemainingForwardDebt (a : ℕ → ℝ) : Prop :=
  Section4SquareOneMainTermCoreHyp a ∧ Section7FiniteIntervalCoreHypWithConst a ∧ LocalU2Hyp a

/--
The stronger pass 46 forward debt implies the weaker pass 47 forward debt.
-/
theorem pass47RemainingForwardDebt_of_pass46
    {a : ℕ → ℝ}
    (hdebt : Pass46RemainingForwardDebt a) :
    Pass47RemainingForwardDebt a := by
  rcases hdebt with ⟨hsec4, hsec7, hU2⟩
  exact ⟨hsec4,
    section7FiniteIntervalCoreHypWithConst_of_pass46 (a := a) hsec7,
    hU2⟩

/--
The pass 47 forward debt already implies the fixed-shift prefix-cancellation conclusion.
-/
theorem conditional_fixed_shift_theorem_of_pass47RemainingForwardDebt
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (hdebt : Pass47RemainingForwardDebt (aShift Λ h)) :
    PrefixLittleO (aShift Λ h) := by
  rcases hdebt with ⟨hsec4, hsec7, hU2⟩
  have hctrl : DirichletMainTermControlOnSquareOne (aShift Λ h) :=
    dirichletMainTermControlOnSquareOne_of_XMainTermControl (a := aShift Λ h) hsec4
  have hbound : BoundedByOne (aShift Λ h) := aShift_boundedByOne Λ h
  have hsqev : EventuallySquareOne (aShift Λ h) := aShift_eventuallySquareOne Λ h
  have hfirst : FirstMomentHyp (aShift Λ h) :=
    firstMoment_of_localU2FourthPower hsec7 hU2
  exact short_interval_first_moment_theorem_squareOneMainTerm hbound hsqev hctrl hfirst

end Pass47LocalU2Constants

section Pass47ActualDebtInterfaces

/--
Pass 47 remaining paper debt: the square-one Section 4 theorem, the paper-faithful Section 7 block
estimate with an absolute constant, the averaged local `U²` hypothesis, and the pass 46 Section 8
single-prime stable-bias endgame core.
-/
def Pass47RemainingPaperDebt
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (liouville a : ℤ → ℂ) (I : Finset ℤ) (α η : ℝ) : Prop :=
  Pass47RemainingForwardDebt (aShift Λ h) ∧
  Section8SinglePrimeBiasStableCoreHyp liouville a h I α η

/--
The pass 46 paper debt implies the weaker pass 47 package.
-/
theorem pass47RemainingPaperDebt_of_pass46
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (liouville a : ℤ → ℂ) (I : Finset ℤ) (α η : ℝ)
    (hdebt : Pass46RemainingPaperDebt Λ h liouville a I α η) :
    Pass47RemainingPaperDebt Λ h liouville a I α η := by
  rcases hdebt with ⟨hforward, hendgame⟩
  exact ⟨pass47RemainingForwardDebt_of_pass46 (a := aShift Λ h) hforward, hendgame⟩

/--
Consequences of the pass 47 paper debt package.
-/
theorem consequences_of_pass47RemainingPaperDebt
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (liouville a : ℤ → ℂ) (I : Finset ℤ) (α η : ℝ)
    (hdebt : Pass47RemainingPaperDebt Λ h liouville a I α η) :
    PrefixLittleO (aShift Λ h) ∧ ∃ J : Finset ℤ, QuadraticObstruction liouville J := by
  rcases hdebt with ⟨hforward, hendgame⟩
  refine ⟨?_, ?_⟩
  · exact conditional_fixed_shift_theorem_of_pass47RemainingForwardDebt Λ h hforward
  · exact quadratic_obstruction_of_section8SinglePrimeBiasStableCore
      liouville a h I α η hendgame

end Pass47ActualDebtInterfaces

end FixedShiftLiouville


/-! ## Pass 48 addendum: exact paper core aliases and one-step branch endgame -/

namespace FixedShiftLiouville

section Pass48ExactPaperAliases

/-- Exact Section 4 paper core in the square-one normalization used by the later argument. -/
def Section4DirichletSquareOneCoreHyp (a : ℕ → ℝ) : Prop :=
  Section4SquareOneMainTermCoreHyp a

/-- Exact Section 7 paper core: Proposition 7.1 in interval-local form with an absolute constant. -/
def Section7Proposition71CoreHyp (a : ℕ → ℝ) : Prop :=
  Section7FiniteIntervalCoreHypWithConst a

/-- The pass 47 forward debt is exactly the pair of paper cores from Sections 4 and 7 together
with the averaged local `U²` input. -/
def Pass48ExactForwardCore (a : ℕ → ℝ) : Prop :=
  Section4DirichletSquareOneCoreHyp a ∧ Section7Proposition71CoreHyp a ∧ LocalU2Hyp a

/-- The pass 48 exact forward core is definitionally the same as the pass 47 forward debt. -/
theorem pass47RemainingForwardDebt_iff_pass48ExactForwardCore
    {a : ℕ → ℝ} :
    Pass47RemainingForwardDebt a ↔ Pass48ExactForwardCore a := by
  rfl

/-- The fixed-shift conclusion through the exact Sections 4 and 7 paper cores. -/
theorem conditional_fixed_shift_theorem_of_pass48ExactForwardCore
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (hcore : Pass48ExactForwardCore (aShift Λ h)) :
    PrefixLittleO (aShift Λ h) := by
  exact conditional_fixed_shift_theorem_of_pass47RemainingForwardDebt Λ h hcore

end Pass48ExactPaperAliases

end FixedShiftLiouville

namespace FixedShiftLiouville
namespace ProjectedPackets

section Pass48OneStepBranch

/--
A completely explicit selected-prime endgame witness:
a chosen prime, a projected top-bias scale, and one concrete dyadic branch step whose defect is at
most the natural twice-the-average threshold.
-/
def SelectedPrimeTopBiasBranchWitness
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ) : Prop :=
  ∃ p : ℕ, Nat.Prime p ∧ IntNotDvd p h ∧ p ≤ primeSelectorCutoff I.card ∧
    η * (divisibleCount I p : ℝ) ≤ ‖divisibleSliceSum a I p α‖ ∧
    ∃ ρ : ℝ, ∃ a₀ : ℤ, ∃ L j k : ℕ,
      0 < L ∧ j < 2^L ∧ k < L ∧
      UnitModulus (projectedSignal liouville α h p) ∧
      ρ ≤ projectedTopMean (projectedSignal liouville α h p) a₀ L ∧
      branchStepDefect (projectedSignal liouville α h p) a₀ L j k
        ≤ ((2 : ℝ) * (1 - ρ) / L)

/--
The pass 46/47 selected-prime top-bias/stable witness already yields an explicit branch step by the
existing greedy-chain selection argument.
-/
theorem selectedPrimeTopBiasBranchWitness_of_selectedPrimeBiasStableWitness
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ)
    (hwitness : SelectedPrimeBiasStableWitness liouville a h I α η) :
    SelectedPrimeTopBiasBranchWitness liouville a h I α η := by
  rcases hwitness with ⟨p, hp, hph, hcut, hslice, ρ, a₀, L, hL, hunit, hbridge⟩
  rcases hbridge with ⟨hρ, _hrigidity⟩
  rcases stableBranchScale_two_average
      (projectedSignal liouville α h p) a₀ L ρ hunit hρ hL with
    ⟨j, hj, k, hk, hsmall⟩
  exact ⟨p, hp, hph, hcut, hslice, ρ, a₀, L, j, k, hL, hj, hk, hunit, hρ, hsmall⟩

/--
Exact one-step Section 8 rigidity interface.
Once one has a selected prime, projected top bias at some dyadic scale, and one explicit dyadic
branch step whose defect is at most the natural threshold `2(1-ρ)/L`, this statement upgrades that
single witness directly to a quadratic obstruction.
-/
def SelectedPrimeBranchRigidityHyp
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ) : Prop :=
  ∀ {p : ℕ} {ρ : ℝ} {a₀ : ℤ} {L j k : ℕ},
    Nat.Prime p →
    IntNotDvd p h →
    p ≤ primeSelectorCutoff I.card →
    η * (divisibleCount I p : ℝ) ≤ ‖divisibleSliceSum a I p α‖ →
    0 < L →
    j < 2^L →
    k < L →
    UnitModulus (projectedSignal liouville α h p) →
    ρ ≤ projectedTopMean (projectedSignal liouville α h p) a₀ L →
    branchStepDefect (projectedSignal liouville α h p) a₀ L j k
      ≤ ((2 : ℝ) * (1 - ρ) / L) →
    ∃ J : Finset ℤ, QuadraticObstruction liouville J

/--
A top-bias branch witness becomes a bias/stable witness once the explicit branch-rigidity
hypothesis from the pass 48 core is retained.  Without that rigidity input this conversion is
not logically valid: the branch witness contains only a small defect step, while the stable witness
contains the bridge from stable scale to quadratic obstruction.
-/
theorem selectedPrimeBiasStableWitness_of_selectedPrimeTopBiasBranchWitness_and_rigidity
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ)
    (hwitness : SelectedPrimeTopBiasBranchWitness liouville a h I α η)
    (hrigidity : SelectedPrimeBranchRigidityHyp liouville a h I α η) :
    SelectedPrimeBiasStableWitness liouville a h I α η := by
  rcases hwitness with
    ⟨p, hp, hph, hcut, hslice, ρ, a₀, L, j, k, hL, hj, hk, hunit, hρ, hsmall⟩
  refine ⟨p, hp, hph, hcut, hslice, ρ, a₀, L, hL, hunit, ?_⟩
  refine ⟨hρ, ?_⟩
  intro hstable
  rcases hstable with ⟨j', hj', k', hk', hsmall'⟩
  exact hrigidity (p := p) (ρ := ρ) (a₀ := a₀) (L := L) (j := j') (k := k')
    hp hph hcut hslice hL hj' hk' hunit hρ hsmall'

/--
The exact explicit selected-prime branch witness forces a quadratic obstruction as soon as the
one-step rigidity interface is available.
-/
theorem quadratic_obstruction_of_selectedPrimeTopBiasBranchWitness
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ)
    (hwitness : SelectedPrimeTopBiasBranchWitness liouville a h I α η)
    (hrigidity : SelectedPrimeBranchRigidityHyp liouville a h I α η) :
    ∃ J : Finset ℤ, QuadraticObstruction liouville J := by
  rcases hwitness with
    ⟨p, hp, hph, hcut, hslice, ρ, a₀, L, j, k, hL, hj, hk, hunit, hρ, hsmall⟩
  exact hrigidity (p := p) (ρ := ρ) (a₀ := a₀) (L := L) (j := j) (k := k) hp hph hcut hslice hL hj hk hunit hρ hsmall

end Pass48OneStepBranch

end ProjectedPackets
end FixedShiftLiouville

namespace FixedShiftLiouville

section Pass48ExactEndgameCore

/-- Exact Section 8 endgame core reduced to a single explicit dyadic branch witness plus a one-step
rigidity upgrade from that witness to a quadratic obstruction. -/
def Section8SinglePrimeOneStepCoreHyp
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ) : Prop :=
  ProjectedPackets.SelectedPrimeTopBiasBranchWitness liouville a h I α η ∧
  ProjectedPackets.SelectedPrimeBranchRigidityHyp liouville a h I α η

/-- The pass 46/47 Section 8 single-prime bias/stable core already supplies the explicit branch
witness part of the pass 48 endgame core. -/
theorem selectedPrimeTopBiasBranchWitness_of_section8SinglePrimeBiasStableCore
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ)
    (hcore : Section8SinglePrimeBiasStableCoreHyp liouville a h I α η) :
    ProjectedPackets.SelectedPrimeTopBiasBranchWitness liouville a h I α η := by
  exact ProjectedPackets.selectedPrimeTopBiasBranchWitness_of_selectedPrimeBiasStableWitness
    liouville a h I α η hcore

/-- The explicit one-step pass 48 Section 8 core gives the quadratic obstruction conclusion. -/
theorem quadratic_obstruction_of_section8SinglePrimeOneStepCore
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ)
    (hcore : Section8SinglePrimeOneStepCoreHyp liouville a h I α η) :
    ∃ J : Finset ℤ, QuadraticObstruction liouville J := by
  rcases hcore with ⟨hwitness, hrigidity⟩
  exact ProjectedPackets.quadratic_obstruction_of_selectedPrimeTopBiasBranchWitness
    liouville a h I α η hwitness hrigidity

/-- The exact pass 48 remaining paper core: Section 4 in square-one Dirichlet form, Section 7 in
Proposition 7.1 local `U²` form, the averaged local `U²` hypothesis, and the explicit Section 8
one-step branch core. -/
def Pass48ExactPaperCore
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (liouville a : ℤ → ℂ) (I : Finset ℤ) (α η : ℝ) : Prop :=
  Pass48ExactForwardCore (aShift Λ h) ∧
  Section8SinglePrimeOneStepCoreHyp liouville a h I α η

/-- Consequences of the exact pass 48 paper core. -/
theorem consequences_of_pass48ExactPaperCore
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (liouville a : ℤ → ℂ) (I : Finset ℤ) (α η : ℝ)
    (hcore : Pass48ExactPaperCore Λ h liouville a I α η) :
    PrefixLittleO (aShift Λ h) ∧ ∃ J : Finset ℤ, QuadraticObstruction liouville J := by
  rcases hcore with ⟨hforward, hendgame⟩
  refine ⟨?_, ?_⟩
  · exact conditional_fixed_shift_theorem_of_pass48ExactForwardCore Λ h hforward
  · exact quadratic_obstruction_of_section8SinglePrimeOneStepCore
      liouville a h I α η hendgame

end Pass48ExactEndgameCore

end FixedShiftLiouville

/-! ## Pass 49 addendum: close Section 7 and replace the pass 48 one-step rigidity by a witness-stable core -/

namespace FixedShiftLiouville

section Pass49Section7Closed

open Complex

/-- Proposition 7.1 is now unconditional in the formal development in its corrected
fourth-power form. -/
theorem section7Proposition71CoreHyp_unconditional
    (a : ℕ → ℝ) :
    Section7Proposition71CoreHyp a := by
  exact intervalLocalU2FourthPowerEstimate_unconditional a

/-- After closing Proposition 7.1, the forward debt reduces to the square-one Section 4 Dirichlet
core together with the averaged local `U²` hypothesis. -/
def Pass49RemainingForwardDebt (a : ℕ → ℝ) : Prop :=
  Section4DirichletSquareOneCoreHyp a ∧ LocalU2Hyp a

/-- The remaining forward debt implies the pass 48 exact forward core because Section 7 is now
available unconditionally. -/
theorem pass48ExactForwardCore_of_pass49RemainingForwardDebt
    {a : ℕ → ℝ}
    (hdebt : Pass49RemainingForwardDebt a) :
    Pass48ExactForwardCore a := by
  rcases hdebt with ⟨hsec4, hU2⟩
  exact ⟨hsec4, section7Proposition71CoreHyp_unconditional a, hU2⟩

/-- Fixed-shift forward conclusion after closing the Section 7 block estimate. -/
theorem conditional_fixed_shift_theorem_of_pass49RemainingForwardDebt
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (hdebt : Pass49RemainingForwardDebt (aShift Λ h)) :
    PrefixLittleO (aShift Λ h) := by
  exact conditional_fixed_shift_theorem_of_pass48ExactForwardCore Λ h
    (pass48ExactForwardCore_of_pass49RemainingForwardDebt (a := aShift Λ h) hdebt)

end Pass49Section7Closed

end FixedShiftLiouville

namespace FixedShiftLiouville
namespace ProjectedPackets

section Pass49ExplicitOneStepStable

/-- A fully witness-specific Section 8 endpoint: one selected prime, explicit top bias, one explicit
small branch step, and the stable-scale bridge at exactly that same selected prime and dyadic
scale. -/
def SelectedPrimeTopBiasBranchStableWitness
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ) : Prop :=
  ∃ p : ℕ, Nat.Prime p ∧ IntNotDvd p h ∧ p ≤ primeSelectorCutoff I.card ∧
    η * (divisibleCount I p : ℝ) ≤ ‖divisibleSliceSum a I p α‖ ∧
    ∃ ρ : ℝ, ∃ a₀ : ℤ, ∃ L j k : ℕ,
      0 < L ∧ j < 2^L ∧ k < L ∧
      UnitModulus (projectedSignal liouville α h p) ∧
      ρ ≤ projectedTopMean (projectedSignal liouville α h p) a₀ L ∧
      branchStepDefect (projectedSignal liouville α h p) a₀ L j k
        ≤ ((2 : ℝ) * (1 - ρ) / L) ∧
      ProjectedBiasQuadraticBridgeStable
        liouville (projectedSignal liouville α h p) a₀ L ρ

/-- The existing single-prime bias/stable witness already furnishes the explicit one-step stable
witness by choosing a small branch step from the stable-scale counting lemma. -/
theorem selectedPrimeTopBiasBranchStableWitness_of_selectedPrimeBiasStableWitness
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ)
    (hwitness : SelectedPrimeBiasStableWitness liouville a h I α η) :
    SelectedPrimeTopBiasBranchStableWitness liouville a h I α η := by
  rcases hwitness with ⟨p, hp, hph, hcut, hslice, ρ, a₀, L, hL, hunit, hbridge⟩
  rcases hbridge with ⟨hρ, hrigidity⟩
  rcases stableBranchScale_two_average
      (projectedSignal liouville α h p) a₀ L ρ hunit hρ hL with
    ⟨j, hj, k, hk, hsmall⟩
  exact ⟨p, hp, hph, hcut, hslice, ρ, a₀, L, j, k, hL, hj, hk, hunit, hρ, hsmall,
    ⟨hρ, hrigidity⟩⟩

theorem selectedPrimeBiasStableWitness_of_selectedPrimeTopBiasBranchStableWitness
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ)
    (hwitness : SelectedPrimeTopBiasBranchStableWitness liouville a h I α η) :
    SelectedPrimeBiasStableWitness liouville a h I α η := by
  rcases hwitness with
    ⟨p, hp, hph, hcut, hslice, ρ, a₀, L, j, k, hL, hj, hk, hunit, hρ, hsmall, hbridge⟩
  exact ⟨p, hp, hph, hcut, hslice, ρ, a₀, L, hL, hunit, hbridge⟩

/-- The explicit one-step stable witness immediately yields a quadratic obstruction, since the
stable-scale bridge is present at the same selected prime and the displayed branch step is itself a
stable branch witness. -/
theorem quadratic_obstruction_of_selectedPrimeTopBiasBranchStableWitness
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ)
    (hwitness : SelectedPrimeTopBiasBranchStableWitness liouville a h I α η) :
    ∃ J : Finset ℤ, QuadraticObstruction liouville J := by
  rcases hwitness with
    ⟨p, hp, hph, hcut, hslice, ρ, a₀, L, j, k, hL, hj, hk, hunit, hρ, hsmall, hbridge⟩
  rcases hbridge with ⟨_hρ', hrigidity⟩
  have hstable :
      StableBranchScale (projectedSignal liouville α h p) a₀ L
        ((2 : ℝ) * (1 - ρ) / L) := by
    exact ⟨j, hj, k, hk, hsmall⟩
  exact hrigidity hstable

end Pass49ExplicitOneStepStable

end ProjectedPackets
end FixedShiftLiouville

namespace FixedShiftLiouville

section Pass49ExactCore

/-- Pass 49 Section 8 core: the explicit selected-prime one-step witness, now packaged together
with the witness-level stable bridge rather than a universal rigidity schema. -/
def Section8ExplicitOneStepStableCoreHyp
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ) : Prop :=
  ProjectedPackets.SelectedPrimeTopBiasBranchStableWitness liouville a h I α η

/-- The pass 46 single-prime bias/stable core implies the explicit pass 49 one-step core. -/
theorem section8ExplicitOneStepStableCoreHyp_of_section8SinglePrimeBiasStableCore
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ)
    (hcore : Section8SinglePrimeBiasStableCoreHyp liouville a h I α η) :
    Section8ExplicitOneStepStableCoreHyp liouville a h I α η := by
  exact ProjectedPackets.selectedPrimeTopBiasBranchStableWitness_of_selectedPrimeBiasStableWitness
    liouville a h I α η hcore

/-- The explicit pass 49 one-step Section 8 core yields a quadratic obstruction. -/
theorem quadratic_obstruction_of_section8ExplicitOneStepStableCore
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ)
    (hcore : Section8ExplicitOneStepStableCoreHyp liouville a h I α η) :
    ∃ J : Finset ℤ, QuadraticObstruction liouville J := by
  exact ProjectedPackets.quadratic_obstruction_of_selectedPrimeTopBiasBranchStableWitness
    liouville a h I α η hcore

/-- After closing Proposition 7.1 and replacing the pass 48 universal rigidity schema by the exact
witness-stable one-step endgame, the remaining paper core is the Section 4 square-one Dirichlet
estimate, the averaged local `U²` hypothesis, and the single-prime Section 8 bias/stable witness
in explicit one-step form. -/
def Pass49ExactPaperCore
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (liouville a : ℤ → ℂ) (I : Finset ℤ) (α η : ℝ) : Prop :=
  Pass49RemainingForwardDebt (aShift Λ h) ∧
  Section8ExplicitOneStepStableCoreHyp liouville a h I α η

/-- The pass 48 exact paper core implies the pass 49 exact core after closing Section 7 and
replacing the universal one-step rigidity interface by the witness-stable one. -/
theorem pass49ExactPaperCore_of_pass48
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (liouville a : ℤ → ℂ) (I : Finset ℤ) (α η : ℝ)
    (hcore : Pass48ExactPaperCore Λ h liouville a I α η) :
    Pass49ExactPaperCore Λ h liouville a I α η := by
  rcases hcore with ⟨hforward, hendgame⟩
  refine ⟨?_, ?_⟩
  · rcases hforward with ⟨hsec4, _hsec7, hU2⟩
    exact ⟨hsec4, hU2⟩
  · rcases hendgame with ⟨hwitness, hrigidity⟩
    have hbias : Section8SinglePrimeBiasStableCoreHyp liouville a h I α η := by
      exact ProjectedPackets.selectedPrimeBiasStableWitness_of_selectedPrimeTopBiasBranchWitness_and_rigidity
        liouville a h I α η hwitness hrigidity
    exact section8ExplicitOneStepStableCoreHyp_of_section8SinglePrimeBiasStableCore
      liouville a h I α η hbias

/-- Consequences of the pass 49 exact core. -/
theorem consequences_of_pass49ExactPaperCore
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (liouville a : ℤ → ℂ) (I : Finset ℤ) (α η : ℝ)
    (hcore : Pass49ExactPaperCore Λ h liouville a I α η) :
    PrefixLittleO (aShift Λ h) ∧ ∃ J : Finset ℤ, QuadraticObstruction liouville J := by
  rcases hcore with ⟨hforward, hendgame⟩
  refine ⟨?_, ?_⟩
  · exact conditional_fixed_shift_theorem_of_pass49RemainingForwardDebt Λ h hforward
  · exact quadratic_obstruction_of_section8ExplicitOneStepStableCore
      liouville a h I α η hendgame

end Pass49ExactCore

end FixedShiftLiouville

/-! ## Pass 50 addendum: collapse the forward chain to square-one first moment, and simplify the
Section 8 residue back to the single-prime bias/stable witness -/

namespace FixedShiftLiouville

section Pass50FirstMomentCore

/-- Exact Section 4 forward core in the form consumed by the Section 6 first-moment theorem. -/
def Section4ShortIntervalMainTermCoreHyp (a : ℕ → ℝ) : Prop :=
  DirichletMainTermControlOnSquareOne a

/-- The pass 49 square-one Dirichlet core is equivalent to the direct short-interval main-term
control used by the first-moment theorem. -/
theorem section4ShortIntervalMainTermCoreHyp_of_dirichletSquareOneCore
    {a : ℕ → ℝ}
    (hcore : Section4DirichletSquareOneCoreHyp a) :
    Section4ShortIntervalMainTermCoreHyp a := by
  exact dirichletMainTermControlOnSquareOne_of_XMainTermControl hcore

/-- Conversely, the short-interval main-term control implies the pass 49 square-one Dirichlet core.
-/
theorem dirichletSquareOneCoreHyp_of_section4ShortIntervalMainTermCore
    {a : ℕ → ℝ}
    (hcore : Section4ShortIntervalMainTermCoreHyp a) :
    Section4DirichletSquareOneCoreHyp a := by
  exact dirichletXMainTermControlOnSquareOne_of_mainTermControl hcore

/-- After Proposition 7.1 is discharged, the averaged local `U²` input is only used through the
first-moment consequence. -/
theorem firstMomentHyp_of_pass49RemainingForwardDebt
    {a : ℕ → ℝ}
    (hdebt : Pass49RemainingForwardDebt a) :
    FirstMomentHyp a := by
  rcases hdebt with ⟨_hsec4, hU2⟩
  exact firstMoment_of_localU2FourthPower
    (intervalLocalU2FourthPowerEstimate_unconditional a) hU2

/-- Exact forward residue after closing Section 7: the square-one main-term theorem and the Section
6 first-moment hypothesis. -/
def Pass50ForwardCore (a : ℕ → ℝ) : Prop :=
  Section4ShortIntervalMainTermCoreHyp a ∧ FirstMomentHyp a

/-- The pass 49 forward debt implies the pass 50 forward core. -/
theorem pass50ForwardCore_of_pass49RemainingForwardDebt
    {a : ℕ → ℝ}
    (hdebt : Pass49RemainingForwardDebt a) :
    Pass50ForwardCore a := by
  rcases hdebt with ⟨hsec4, hU2⟩
  refine ⟨section4ShortIntervalMainTermCoreHyp_of_dirichletSquareOneCore hsec4, ?_⟩
  exact firstMoment_of_localU2FourthPower
    (intervalLocalU2FourthPowerEstimate_unconditional a) hU2

/-- Fixed-shift forward conclusion from the exact square-one first-moment core. -/
theorem conditional_fixed_shift_theorem_of_pass50ForwardCore
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (hcore : Pass50ForwardCore (aShift Λ h)) :
    PrefixLittleO (aShift Λ h) := by
  rcases hcore with ⟨hctrl, hfirst⟩
  have hbound : BoundedByOne (aShift Λ h) := aShift_boundedByOne Λ h
  have hsqev : EventuallySquareOne (aShift Λ h) := aShift_eventuallySquareOne Λ h
  exact short_interval_first_moment_theorem_squareOneMainTerm hbound hsqev hctrl hfirst

end Pass50FirstMomentCore

section Pass50ExactPaperCore

/-- The exact pass 49 endgame witness is equivalent to the more compact single-prime top-bias /
stable witness from pass 46. -/
theorem section8SinglePrimeBiasStableCoreHyp_of_section8ExplicitOneStepStableCore
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ)
    (hcore : Section8ExplicitOneStepStableCoreHyp liouville a h I α η) :
    Section8SinglePrimeBiasStableCoreHyp liouville a h I α η := by
  exact ProjectedPackets.selectedPrimeBiasStableWitness_of_selectedPrimeTopBiasBranchStableWitness
    liouville a h I α η hcore

/-- Exact pass 50 paper core: Section 4 in direct square-one main-term form, Section 6 first
moment, and Section 8 in compact single-prime bias/stable form. -/
def Pass50ExactPaperCore
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (liouville a : ℤ → ℂ) (I : Finset ℤ) (α η : ℝ) : Prop :=
  Pass50ForwardCore (aShift Λ h) ∧
  Section8SinglePrimeBiasStableCoreHyp liouville a h I α η

/-- The pass 49 exact paper core implies the pass 50 exact paper core. -/
theorem pass50ExactPaperCore_of_pass49
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (liouville a : ℤ → ℂ) (I : Finset ℤ) (α η : ℝ)
    (hcore : Pass49ExactPaperCore Λ h liouville a I α η) :
    Pass50ExactPaperCore Λ h liouville a I α η := by
  rcases hcore with ⟨hforward, hendgame⟩
  refine ⟨pass50ForwardCore_of_pass49RemainingForwardDebt hforward, ?_⟩
  exact section8SinglePrimeBiasStableCoreHyp_of_section8ExplicitOneStepStableCore
    liouville a h I α η hendgame

/-- Consequences of the exact pass 50 paper core. -/
theorem consequences_of_pass50ExactPaperCore
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (liouville a : ℤ → ℂ) (I : Finset ℤ) (α η : ℝ)
    (hcore : Pass50ExactPaperCore Λ h liouville a I α η) :
    PrefixLittleO (aShift Λ h) ∧ ∃ J : Finset ℤ, QuadraticObstruction liouville J := by
  rcases hcore with ⟨hforward, hendgame⟩
  refine ⟨?_, ?_⟩
  · exact conditional_fixed_shift_theorem_of_pass50ForwardCore Λ h hforward
  · exact quadratic_obstruction_of_section8SinglePrimeBiasStableCore
      liouville a h I α η hendgame

end Pass50ExactPaperCore

end FixedShiftLiouville

/-! ## Pass 51 addendum: collapse to the shortest theorem-consumed forward and endgame cores -/

namespace FixedShiftLiouville

section Pass51TheoremConsumedCore

/-- After Section 6 is routed through shells, the forward theorem only consumes the square-one
main-term control together with dyadic local quartic control. -/
def Pass51ForwardCore (a : ℕ → ℝ) : Prop :=
  Section4ShortIntervalMainTermCoreHyp a ∧ DyadicLocalQuarticHyp a

/-- The pass 50 forward core implies the exact dyadic-local form actually consumed by the forward
criterion, once the ambient boundedness hypothesis is supplied. -/
theorem pass51ForwardCore_of_pass50ForwardCore
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    (hcore : Pass50ForwardCore a) :
    Pass51ForwardCore a := by
  rcases hcore with ⟨hctrl, hfirst⟩
  exact ⟨hctrl, dyadicLocalQuartic_of_firstMoment ha hfirst⟩

/-- Fixed-shift forward conclusion from the shortest theorem-consumed forward core. -/
theorem conditional_fixed_shift_theorem_of_pass51ForwardCore
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (hcore : Pass51ForwardCore (aShift Λ h)) :
    PrefixLittleO (aShift Λ h) := by
  rcases hcore with ⟨hctrl, hdyadic⟩
  have hbound : BoundedByOne (aShift Λ h) := aShift_boundedByOne Λ h
  have hsqev : EventuallySquareOne (aShift Λ h) := aShift_eventuallySquareOne Λ h
  exact dyadic_local_quartic_criterion_squareOneMainTerm hbound hsqev hctrl hdyadic

/-- The endgame theorem only consumes the existence of a quadratic obstruction. -/
def Section8ObstructionCoreHyp (liouville : ℤ → ℂ) : Prop :=
  ∃ J : Finset ℤ, QuadraticObstruction liouville J

/-- The pass 50 single-prime bias/stable core already gives the exact endgame consequence consumed
later. -/
theorem section8ObstructionCoreHyp_of_section8SinglePrimeBiasStableCore
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ)
    (hcore : Section8SinglePrimeBiasStableCoreHyp liouville a h I α η) :
    Section8ObstructionCoreHyp liouville := by
  exact quadratic_obstruction_of_section8SinglePrimeBiasStableCore liouville a h I α η hcore

/-- Exact theorem-consumed core after passes 49 and 50: the forward side is reduced to the dyadic
quartic criterion input, and the endgame side is reduced to existence of a quadratic obstruction. -/
def Pass51TheoremConsumedCore
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (liouville : ℤ → ℂ) : Prop :=
  Pass51ForwardCore (aShift Λ h) ∧ Section8ObstructionCoreHyp liouville

/-- The pass 50 exact paper core implies the exact theorem-consumed core. -/
theorem pass51TheoremConsumedCore_of_pass50ExactPaperCore
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (liouville a : ℤ → ℂ) (I : Finset ℤ) (α η : ℝ)
    (hcore : Pass50ExactPaperCore Λ h liouville a I α η) :
    Pass51TheoremConsumedCore Λ h liouville := by
  rcases hcore with ⟨hforward, hendgame⟩
  refine ⟨?_, ?_⟩
  · rcases hforward with ⟨hctrl, hfirst⟩
    refine ⟨hctrl, ?_⟩
    have hbound : BoundedByOne (aShift Λ h) := aShift_boundedByOne Λ h
    exact dyadicLocalQuartic_of_firstMoment hbound hfirst
  · exact quadratic_obstruction_of_section8SinglePrimeBiasStableCore
      liouville a h I α η hendgame

/-- Consequences of the exact theorem-consumed core. -/
theorem consequences_of_pass51TheoremConsumedCore
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (liouville : ℤ → ℂ)
    (hcore : Pass51TheoremConsumedCore Λ h liouville) :
    PrefixLittleO (aShift Λ h) ∧ ∃ J : Finset ℤ, QuadraticObstruction liouville J := by
  rcases hcore with ⟨hforward, hobstr⟩
  refine ⟨conditional_fixed_shift_theorem_of_pass51ForwardCore Λ h hforward, hobstr⟩

end Pass51TheoremConsumedCore

end FixedShiftLiouville


namespace FixedShiftLiouville

section Pass52TheoremConsumedCore

/--
The exact forward input consumed by the Section 4 slope criterion is the refined square-one main-term
control together with the positive multiscale hypothesis.
-/
def Pass52ForwardCore (a : ℕ → ℝ) : Prop :=
  Section4ShortIntervalMainTermCoreHyp a ∧ PositiveMultiscaleHyp a

/--
The pass 50 forward core already implies the exact Section 4-consumed forward core.
-/
theorem pass52ForwardCore_of_pass50ForwardCore
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    (hsqev : EventuallySquareOne a)
    (hcore : Pass50ForwardCore a) :
    Pass52ForwardCore a := by
  rcases hcore with ⟨hctrl, hfirst⟩
  refine ⟨hctrl, ?_⟩
  have hdyadic : DyadicLocalQuarticHyp a :=
    dyadicLocalQuartic_of_firstMoment ha hfirst
  exact positiveMultiscale_of_dyadicLocalQuartic ha hsqev hdyadic

/--
The pass 51 forward core factors through the exact Section 4-consumed forward core.
-/
theorem pass52ForwardCore_of_pass51ForwardCore
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    (hsqev : EventuallySquareOne a)
    (hcore : Pass51ForwardCore a) :
    Pass52ForwardCore a := by
  rcases hcore with ⟨hctrl, hdyadic⟩
  refine ⟨hctrl, ?_⟩
  exact positiveMultiscale_of_dyadicLocalQuartic ha hsqev hdyadic

/--
The fixed-shift theorem from the exact Section 4-consumed forward core.
-/
theorem conditional_fixed_shift_theorem_of_pass52ForwardCore
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (hcore : Pass52ForwardCore (aShift Λ h)) :
    PrefixLittleO (aShift Λ h) := by
  rcases hcore with ⟨hctrl, hmulti⟩
  have hbound : BoundedByOne (aShift Λ h) := aShift_boundedByOne Λ h
  have hsqev : EventuallySquareOne (aShift Λ h) := aShift_eventuallySquareOne Λ h
  have hslope : UniformSlopeHyp (aShift Λ h) :=
    uniformSlope_of_dirichletMainTermControlOnSquareOne
      (a := aShift Λ h) hbound hsqev hctrl hmulti
  exact uniform_slope_criterion (a := aShift Λ h) hbound hsqev hslope

/--
The exact theorem-consumed core after collapsing the forward side to the Section 4 slope input.
-/
def Pass52TheoremConsumedCore
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (liouville : ℤ → ℂ) : Prop :=
  Pass52ForwardCore (aShift Λ h) ∧ Section8ObstructionCoreHyp liouville

/--
The pass 51 theorem-consumed core implies the exact pass 52 theorem-consumed core.
-/
theorem pass52TheoremConsumedCore_of_pass51TheoremConsumedCore
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (liouville : ℤ → ℂ)
    (hcore : Pass51TheoremConsumedCore Λ h liouville) :
    Pass52TheoremConsumedCore Λ h liouville := by
  rcases hcore with ⟨hforward, hobstr⟩
  refine ⟨?_, hobstr⟩
  have hbound : BoundedByOne (aShift Λ h) := aShift_boundedByOne Λ h
  have hsqev : EventuallySquareOne (aShift Λ h) := aShift_eventuallySquareOne Λ h
  exact pass52ForwardCore_of_pass51ForwardCore hbound hsqev hforward

/--
Consequences of the pass 52 theorem-consumed core.
-/
theorem consequences_of_pass52TheoremConsumedCore
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (liouville : ℤ → ℂ)
    (hcore : Pass52TheoremConsumedCore Λ h liouville) :
    PrefixLittleO (aShift Λ h) ∧ ∃ J : Finset ℤ, QuadraticObstruction liouville J := by
  rcases hcore with ⟨hforward, hobstr⟩
  exact ⟨conditional_fixed_shift_theorem_of_pass52ForwardCore Λ h hforward, hobstr⟩

end Pass52TheoremConsumedCore

end FixedShiftLiouville


namespace FixedShiftLiouville

section Pass53TheoremConsumedCore

/--
The shortest forward-side input actually consumed by the existing fixed-shift proof is the
uniform-slope hypothesis itself.
-/
def Pass53ForwardCore (a : ℕ → ℝ) : Prop :=
  UniformSlopeHyp a

/--
The pass 52 forward core implies the exact theorem-consumed forward input.
-/
theorem pass53ForwardCore_of_pass52ForwardCore
    {a : ℕ → ℝ}
    (ha : BoundedByOne a)
    (hsqev : EventuallySquareOne a)
    (hcore : Pass52ForwardCore a) :
    Pass53ForwardCore a := by
  rcases hcore with ⟨hctrl, hmulti⟩
  exact uniformSlope_of_dirichletMainTermControlOnSquareOne
    (a := a) ha hsqev hctrl hmulti

/--
The fixed-shift theorem from the minimal forward input already consumed by the proof.
-/
theorem conditional_fixed_shift_theorem_of_pass53ForwardCore
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (hcore : Pass53ForwardCore (aShift Λ h)) :
    PrefixLittleO (aShift Λ h) := by
  have hbound : BoundedByOne (aShift Λ h) := aShift_boundedByOne Λ h
  have hsqev : EventuallySquareOne (aShift Λ h) := aShift_eventuallySquareOne Λ h
  exact uniform_slope_criterion (a := aShift Λ h) hbound hsqev hcore

/--
The exact theorem-consumed core after collapsing the forward side all the way to uniform slope.
-/
def Pass53TheoremConsumedCore
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (liouville : ℤ → ℂ) : Prop :=
  Pass53ForwardCore (aShift Λ h) ∧ Section8ObstructionCoreHyp liouville

/--
The pass 52 theorem-consumed core factors through the exact theorem-consumed core.
-/
theorem pass53TheoremConsumedCore_of_pass52TheoremConsumedCore
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (liouville : ℤ → ℂ)
    (hcore : Pass52TheoremConsumedCore Λ h liouville) :
    Pass53TheoremConsumedCore Λ h liouville := by
  rcases hcore with ⟨hforward, hobstr⟩
  refine ⟨?_, hobstr⟩
  have hbound : BoundedByOne (aShift Λ h) := aShift_boundedByOne Λ h
  have hsqev : EventuallySquareOne (aShift Λ h) := aShift_eventuallySquareOne Λ h
  exact pass53ForwardCore_of_pass52ForwardCore hbound hsqev hforward

/--
Consequences of the exact theorem-consumed core in pass 53.
-/
theorem consequences_of_pass53TheoremConsumedCore
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (liouville : ℤ → ℂ)
    (hcore : Pass53TheoremConsumedCore Λ h liouville) :
    PrefixLittleO (aShift Λ h) ∧ ∃ J : Finset ℤ, QuadraticObstruction liouville J := by
  rcases hcore with ⟨hforward, hobstr⟩
  exact ⟨conditional_fixed_shift_theorem_of_pass53ForwardCore Λ h hforward, hobstr⟩

end Pass53TheoremConsumedCore

end FixedShiftLiouville

/-! ## Pass 54 addendum: close the remaining packaging and expose the terminal conclusion -/

namespace FixedShiftLiouville

section Pass54ClosedConclusion

/--
The terminal closed conclusion of the present development: forward prefix cancellation together
with existence of a quadratic obstruction.
-/
def Pass54ClosedConclusion
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (liouville : ℤ → ℂ) : Prop :=
  PrefixLittleO (aShift Λ h) ∧ ∃ J : Finset ℤ, QuadraticObstruction liouville J

/--
The terminal conclusion follows directly from the exact theorem-consumed pass 53 core, with no
additional packaging.
-/
theorem pass54ClosedConclusion_of_pass53TheoremConsumedCore
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (liouville : ℤ → ℂ)
    (hcore : Pass53TheoremConsumedCore Λ h liouville) :
    Pass54ClosedConclusion Λ h liouville := by
  exact consequences_of_pass53TheoremConsumedCore Λ h liouville hcore

/--
A fully unpacked terminal theorem: uniform slope on the shifted sequence and any quadratic
obstruction witness already yield the final closed conclusion.
-/
theorem pass54ClosedConclusion_of_uniformSlope_and_obstruction
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (liouville : ℤ → ℂ)
    (hforward : UniformSlopeHyp (aShift Λ h))
    (hobstr : ∃ J : Finset ℤ, QuadraticObstruction liouville J) :
    Pass54ClosedConclusion Λ h liouville := by
  refine ⟨conditional_fixed_shift_theorem_of_pass53ForwardCore Λ h hforward, hobstr⟩

/--
The pass 52 theorem-consumed core factors all the way to the terminal conclusion.
-/
theorem pass54ClosedConclusion_of_pass52TheoremConsumedCore
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (liouville : ℤ → ℂ)
    (hcore : Pass52TheoremConsumedCore Λ h liouville) :
    Pass54ClosedConclusion Λ h liouville := by
  exact consequences_of_pass52TheoremConsumedCore Λ h liouville hcore

/--
The pass 51 theorem-consumed core factors all the way to the terminal conclusion.
-/
theorem pass54ClosedConclusion_of_pass51TheoremConsumedCore
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (liouville : ℤ → ℂ)
    (hcore : Pass51TheoremConsumedCore Λ h liouville) :
    Pass54ClosedConclusion Λ h liouville := by
  exact consequences_of_pass51TheoremConsumedCore Λ h liouville hcore

/--
The exact pass 50 paper core already implies the terminal conclusion.
-/
theorem pass54ClosedConclusion_of_pass50ExactPaperCore
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (liouville a : ℤ → ℂ) (I : Finset ℤ) (α η : ℝ)
    (hcore : Pass50ExactPaperCore Λ h liouville a I α η) :
    Pass54ClosedConclusion Λ h liouville := by
  exact consequences_of_pass50ExactPaperCore Λ h liouville a I α η hcore

/--
The actual remaining paper debt package implies the same terminal conclusion.
-/
theorem pass54ClosedConclusion_of_actualRemainingPaperDebt
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (liouville a : ℤ → ℂ) (I : Finset ℤ) (α η : ℝ)
    (hη : 0 ≤ η)
    (hdebt : ActualRemainingPaperDebt Λ h liouville a I α η) :
    Pass54ClosedConclusion Λ h liouville := by
  exact consequences_of_actualRemainingPaperDebt Λ h liouville a I α η hη hdebt

end Pass54ClosedConclusion

end FixedShiftLiouville

namespace FixedShiftLiouville
namespace ProjectedPackets

/-- The additive character has unit norm. -/
lemma norm_eReal (x : ℝ) : ‖eReal x‖ = 1 := by
  simp [eReal]

/-- The quadratic packet has the same norm as the underlying Liouville phase. -/
lemma norm_gPacket
    (liouville : ℤ → ℂ) (α : ℝ) (h n : ℤ) :
    ‖gPacket liouville α h n‖ = ‖liouville n‖ := by
  unfold gPacket
  rw [norm_mul, norm_eReal, mul_one]

/-- The projected signal records the product of two Liouville magnitudes. -/
lemma norm_projectedSignal
    (liouville : ℤ → ℂ) (α : ℝ) (h : ℤ) (p : ℕ) (n : ℤ) :
    ‖projectedSignal liouville α h p n‖ =
      ‖liouville ((p : ℤ) * (n + h))‖ * ‖liouville ((p : ℤ) * n)‖ := by
  unfold projectedSignal
  simp [norm_mul, norm_eReal, norm_gPacket, norm_star, mul_assoc, mul_comm, mul_left_comm]

/-- A unit-modulus projected signal forces at least one underlying Liouville value to have norm
at least `1`. -/
theorem exists_large_liouville_value_of_projectedSignal_unitModulus
    (liouville : ℤ → ℂ) (α : ℝ) (h : ℤ) (p : ℕ)
    (hunit : UnitModulus (projectedSignal liouville α h p)) :
    ∃ n : ℤ, 1 ≤ ‖liouville n‖ := by
  have h0 : ‖projectedSignal liouville α h p 0‖ = 1 := hunit 0
  have hprod : ‖liouville ((p : ℤ) * h)‖ * ‖liouville 0‖ = 1 := by
    simpa [norm_projectedSignal] using h0
  by_cases hzero : 1 ≤ ‖liouville 0‖
  · exact ⟨0, hzero⟩
  · refine ⟨(p : ℤ) * h, ?_⟩
    have hzero' : ‖liouville 0‖ < 1 := lt_of_not_ge hzero
    have hnonneg0 : 0 ≤ ‖liouville 0‖ := norm_nonneg _
    have hnonnegph : 0 ≤ ‖liouville ((p : ℤ) * h)‖ := norm_nonneg _
    nlinarith

/-- Any single Liouville value of norm at least `1` already gives a local quadratic obstruction,
by taking a singleton interval and the zero polynomial. -/
theorem quadraticObstruction_singleton_of_norm_ge_one
    (liouville : ℤ → ℂ) {n : ℤ}
    (hn : 1 ≤ ‖liouville n‖) :
    ∃ I : Finset ℤ, QuadraticObstruction liouville I := by
  refine ⟨{n}, ?_⟩
  unfold QuadraticObstruction
  refine ⟨fun _ => 0, ?_⟩
  constructor
  · refine ⟨0, 0, 0, ?_⟩
    intro m
    ring
  · simpa [eReal] using hn

/-- Hence a unit-modulus projected signal already implies a quadratic obstruction. -/
theorem quadratic_obstruction_of_projectedSignal_unitModulus
    (liouville : ℤ → ℂ) (α : ℝ) (h : ℤ) (p : ℕ)
    (hunit : UnitModulus (projectedSignal liouville α h p)) :
    ∃ I : Finset ℤ, QuadraticObstruction liouville I := by
  rcases exists_large_liouville_value_of_projectedSignal_unitModulus liouville α h p hunit with
    ⟨n, hn⟩
  exact quadraticObstruction_singleton_of_norm_ge_one liouville hn

end ProjectedPackets
end FixedShiftLiouville

namespace FixedShiftLiouville

section Pass55UnitModulusCore

/-- Minimal surviving Section 8 residue after extracting the only part actually needed for the
terminal obstruction: existence of one projected prime slice whose projected signal has unit
modulus. -/
def Section8PureUnitModulusCoreHyp
    (liouville : ℤ → ℂ) (h : ℤ) (α : ℝ) : Prop :=
  ∃ p : ℕ, UnitModulus (projectedSignal liouville α h p)

/-- The pass 46 single-prime bias/stable core already contains the pure unit-modulus residue. -/
theorem section8PureUnitModulusCoreHyp_of_section8SinglePrimeBiasStableCore
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ)
    (hcore : Section8SinglePrimeBiasStableCoreHyp liouville a h I α η) :
    Section8PureUnitModulusCoreHyp liouville h α := by
  rcases hcore with ⟨p, hp, hph, hcut, hslice, ρ, a₀, L, hL, hunit, hbias⟩
  exact ⟨p, hunit⟩

/-- The earlier actual Section 8 debt also contains the same pure unit-modulus residue. -/
theorem section8PureUnitModulusCoreHyp_of_actualRemainingEndgameDebt
    (liouville a : ℤ → ℂ) (h : ℤ) (I : Finset ℤ) (α η : ℝ)
    (hη : 0 ≤ η)
    (hendgame : ActualRemainingEndgameDebt liouville a h I α η) :
    Section8PureUnitModulusCoreHyp liouville h α := by
  have hstable : ProjectedPackets.RemainingBottleneckSelectedPrimeStableHyp liouville a h I α η := by
    exact remainingBottleneckSelectedPrimeStableHyp_of_section8SelectorRigidityCore
      liouville a h I α η hη hendgame
  have hwitness : Section8SinglePrimeBiasStableCoreHyp liouville a h I α η := by
    exact ProjectedPackets.selectedPrimeBiasStableWitness_of_remainingBottleneckSelectedPrimeStable
      liouville a h I α η hstable
  exact section8PureUnitModulusCoreHyp_of_section8SinglePrimeBiasStableCore
    liouville a h I α η hwitness

/-- The pure unit-modulus residue already implies the exact endgame obstruction core. -/
theorem section8ObstructionCoreHyp_of_section8PureUnitModulusCore
    (liouville : ℤ → ℂ) (h : ℤ) (α : ℝ)
    (hcore : Section8PureUnitModulusCoreHyp liouville h α) :
    Section8ObstructionCoreHyp liouville := by
  rcases hcore with ⟨p, hunit⟩
  exact ProjectedPackets.quadratic_obstruction_of_projectedSignal_unitModulus
    liouville α h p hunit

/-- Exact terminal core after the Section 8 collapse to pure unit-modulus. -/
def Pass55Core
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (liouville : ℤ → ℂ)
    (α : ℝ) : Prop :=
  UniformSlopeHyp (aShift Λ h) ∧ Section8PureUnitModulusCoreHyp liouville h α

/-- The pass 50 exact paper core factors through the pass 55 terminal core. -/
theorem pass55Core_of_pass50ExactPaperCore
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (liouville a : ℤ → ℂ) (I : Finset ℤ) (α η : ℝ)
    (hcore : Pass50ExactPaperCore Λ h liouville a I α η) :
    Pass55Core Λ h liouville α := by
  rcases hcore with ⟨hforward, hendgame⟩
  have hbound : BoundedByOne (aShift Λ h) := aShift_boundedByOne Λ h
  have hsqev : EventuallySquareOne (aShift Λ h) := aShift_eventuallySquareOne Λ h
  have h51 : Pass51ForwardCore (aShift Λ h) := by
    exact pass51ForwardCore_of_pass50ForwardCore hbound hforward
  have h52 : Pass52ForwardCore (aShift Λ h) := by
    exact pass52ForwardCore_of_pass51ForwardCore hbound hsqev h51
  have h53 : Pass53ForwardCore (aShift Λ h) := by
    exact pass53ForwardCore_of_pass52ForwardCore hbound hsqev h52
  refine ⟨h53, ?_⟩
  exact section8PureUnitModulusCoreHyp_of_section8SinglePrimeBiasStableCore
    liouville a h I α η hendgame

/-- Terminal conclusion from the exact pass 55 core. -/
theorem pass54ClosedConclusion_of_pass55Core
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (liouville : ℤ → ℂ)
    (α : ℝ)
    (hcore : Pass55Core Λ h liouville α) :
    Pass54ClosedConclusion Λ h liouville := by
  rcases hcore with ⟨hforward, hendgame⟩
  exact pass54ClosedConclusion_of_uniformSlope_and_obstruction
    Λ h liouville hforward
    (section8ObstructionCoreHyp_of_section8PureUnitModulusCore liouville h α hendgame)

/-- Reproved terminal theorem: the pass 50 exact paper core now factors through uniform slope plus
pure projected-signal unit modulus, with no use of the Section 8 rigidity/bias payload beyond
extracting that unit-modulus witness. -/
theorem pass54ClosedConclusion_of_pass50ExactPaperCore_via_pass55
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (liouville a : ℤ → ℂ) (I : Finset ℤ) (α η : ℝ)
    (hcore : Pass50ExactPaperCore Λ h liouville a I α η) :
    Pass54ClosedConclusion Λ h liouville := by
  exact pass54ClosedConclusion_of_pass55Core Λ h liouville α
    (pass55Core_of_pass50ExactPaperCore Λ h liouville a I α η hcore)


end Pass55UnitModulusCore

end FixedShiftLiouville

/-! ## Pass 56 addendum: remove the final forward wrapper and state the terminal theorem
    directly from square-one main-term control, positive multiscale input, and pure unit modulus -/

namespace FixedShiftLiouville

section Pass56DirectTerminalCore

/--
The terminal direct core after eliminating the forward wrapper `UniformSlopeHyp`:
we keep exactly the square-one Dirichlet main-term input and the positive multiscale input used
by the uniform-slope argument, together with the pure projected-signal unit-modulus endgame core.
-/
def Pass56DirectCore
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (liouville : ℤ → ℂ)
    (α : ℝ) : Prop :=
  DirichletMainTermControlOnSquareOne (aShift Λ h) ∧
  PositiveMultiscaleHyp (aShift Λ h) ∧
  Section8PureUnitModulusCoreHyp liouville h α

/--
Direct terminal theorem from the exact square-one Section 4 input, positive multiscale control,
and a pure projected-signal unit-modulus witness.
-/
theorem pass54ClosedConclusion_of_pass56DirectCore
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (liouville : ℤ → ℂ)
    (α : ℝ)
    (hcore : Pass56DirectCore Λ h liouville α) :
    Pass54ClosedConclusion Λ h liouville := by
  rcases hcore with ⟨hctrl, hmulti, hendgame⟩
  have hforward : Pass52ForwardCore (aShift Λ h) := ⟨hctrl, hmulti⟩
  have hprefix : PrefixLittleO (aShift Λ h) :=
    conditional_fixed_shift_theorem_of_pass52ForwardCore Λ h hforward
  have hobstr : ∃ J : Finset ℤ, QuadraticObstruction liouville J :=
    section8ObstructionCoreHyp_of_section8PureUnitModulusCore liouville h α hendgame
  exact ⟨hprefix, hobstr⟩

/--
Fully unpacked direct terminal theorem with no intermediate wrapper definitions.
-/
theorem pass54ClosedConclusion_of_dirichletMainTermControlOnSquareOne_and_positiveMultiscale_and_unitModulus
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (liouville : ℤ → ℂ)
    (α : ℝ)
    (hctrl : DirichletMainTermControlOnSquareOne (aShift Λ h))
    (hmulti : PositiveMultiscaleHyp (aShift Λ h))
    (hendgame : Section8PureUnitModulusCoreHyp liouville h α) :
    Pass54ClosedConclusion Λ h liouville := by
  exact pass54ClosedConclusion_of_pass56DirectCore Λ h liouville α
    ⟨hctrl, hmulti, hendgame⟩

/--
The exact pass 50 paper core factors through the direct terminal core of pass 56.
-/
theorem pass56DirectCore_of_pass50ExactPaperCore
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (liouville a : ℤ → ℂ)
    (I : Finset ℤ)
    (α η : ℝ)
    (hcore : Pass50ExactPaperCore Λ h liouville a I α η) :
    Pass56DirectCore Λ h liouville α := by
  rcases hcore with ⟨hforward, hendgame⟩
  have hbound : BoundedByOne (aShift Λ h) := aShift_boundedByOne Λ h
  have hsqev : EventuallySquareOne (aShift Λ h) := aShift_eventuallySquareOne Λ h
  have h52 : Pass52ForwardCore (aShift Λ h) :=
    pass52ForwardCore_of_pass50ForwardCore hbound hsqev hforward
  rcases h52 with ⟨hctrl, hmulti⟩
  refine ⟨hctrl, hmulti, ?_⟩
  exact section8PureUnitModulusCoreHyp_of_section8SinglePrimeBiasStableCore
    liouville a h I α η hendgame

/--
Direct reproving of the terminal conclusion from the exact pass 50 paper core, with the forward
side now routed through square-one Dirichlet main-term control and positive multiscale input
rather than the wrapper `UniformSlopeHyp`.
-/
theorem pass54ClosedConclusion_of_pass50ExactPaperCore_via_pass56
    (Λ : ℤ → ℤ) [LiouvilleLike Λ]
    (h : ℤ)
    (liouville a : ℤ → ℂ)
    (I : Finset ℤ)
    (α η : ℝ)
    (hcore : Pass50ExactPaperCore Λ h liouville a I α η) :
    Pass54ClosedConclusion Λ h liouville := by
  exact pass54ClosedConclusion_of_pass56DirectCore Λ h liouville α
    (pass56DirectCore_of_pass50ExactPaperCore Λ h liouville a I α η hcore)

end Pass56DirectTerminalCore

end FixedShiftLiouville

end
