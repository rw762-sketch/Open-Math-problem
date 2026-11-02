/-
Every odd distinct covering system has at least five distinct primes in its lcm.

From `towerSum_le_bff`: `T(L) ≤ D(P) := ∏_{p∈P}(1 + x_p) − 1 − ∑_{p∈P} x_p` with `x_p = 1/(p−2)`.
Induction on the primes in increasing order: the `k`-th smallest odd prime is at least the `k`-th
of `3, 5, 7, 11`, so `x` is bounded coordinatewise and `D(P) ≤ 41/45 < 1` whenever `|P| ≤ 4`.
This is Hackmon's four-prime theorem (and the `ω ≥ 5` consequence of Berger–Felzenbaum–Fraenkel).
-/
import Covering.BFF

namespace Covering

open Finset

/-- `D(s, x) = ∏ (1 + x_i) − 1 − ∑ x_i`. -/
noncomputable def bffD (s : Finset ℕ) (x : ℕ → ℚ) : ℚ := ∏ i ∈ s, (1 + x i) - 1 - ∑ i ∈ s, x i

/-- The BFF weight `x_p = 1/(p−2)`. -/
noncomputable def xw (p : ℕ) : ℚ := 1 / ((p : ℚ) - 2)

theorem towerSum_le_bffD {L : ℕ} (hL : 0 < L) (hodd : Odd L) :
    towerSum L ≤ bffD L.primeFactors xw := by
  have h := towerSum_le_bff hL hodd
  unfold bffD xw
  have h7 : ∏ p ∈ L.primeFactors, (1 + 1 / ((p : ℚ) - 2)) =
      ∏ p ∈ L.primeFactors, ((p : ℚ) - 1) / ((p : ℚ) - 2) := by
    apply prod_congr rfl
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (Nat.dvd_of_mem_primeFactors hp))
    have : (3 : ℚ) ≤ p := by have := hpp.two_le; exact_mod_cast (by omega : 3 ≤ p)
    have h2 : (p : ℚ) - 2 ≠ 0 := by linarith
    field_simp
    ring
  rw [h7]
  exact h

theorem bffD_insert {s : Finset ℕ} {a : ℕ} (ha : a ∉ s) (x : ℕ → ℚ) :
    bffD (insert a s) x = (1 + x a) * bffD s x + x a * ∑ i ∈ s, x i := by
  unfold bffD
  rw [prod_insert ha, sum_insert ha]
  ring

theorem bffD_nonneg {s : Finset ℕ} {x : ℕ → ℚ} (h0 : ∀ i ∈ s, 0 ≤ x i) : 0 ≤ bffD s x :=
  (D_mono s x x h0 (fun i _ => le_rfl)).1

/-- Lower bounds for the `k`-th smallest odd prime, `k ≤ 4`. -/
def qk : ℕ → ℕ
  | 0 => 1
  | 1 => 3
  | 2 => 5
  | 3 => 7
  | _ => 11

/-- Upper bounds `c_k ≥ D` and `S_k ≥ ∑ x` for `k` odd primes, `k ≤ 4`. -/
noncomputable def ck : ℕ → ℚ
  | 0 => 0
  | 1 => 0
  | 2 => 1 / 3
  | 3 => 2 / 3
  | _ => 41 / 45

noncomputable def Sk : ℕ → ℚ
  | 0 => 0
  | 1 => 1
  | 2 => 4 / 3
  | 3 => 23 / 15
  | _ => 23 / 15 + 1 / 9

theorem not_prime_nine : ¬ Nat.Prime 9 := by decide

/-- Main induction: for a set `s` of at most four odd primes,
`D(s) ≤ c_{|s|}`, `∑ x ≤ S_{|s|}`, and (if nonempty) `s` has an element `≥ q_{|s|}`. -/
theorem bff_four_induction (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime ∧ Odd p) (hcard : s.card ≤ 4) :
    bffD s xw ≤ ck s.card ∧ (∑ p ∈ s, xw p) ≤ Sk s.card ∧
      (s = ∅ ∨ ∃ b ∈ s, qk s.card ≤ b) := by
  classical
  induction s using Finset.induction_on_max with
  | h0 => simp [bffD, ck, Sk]
  | step a s hlt ih =>
    have ha : a ∉ s := fun h => lt_irrefl a (hlt a h)
    have hs' : ∀ p ∈ s, p.Prime ∧ Odd p := fun p hp => hs p (mem_insert_of_mem hp)
    rw [card_insert_of_notMem ha] at hcard ⊢
    have hk : s.card ≤ 4 := by omega
    obtain ⟨ihD, ihS, ihq⟩ := ih hs' hk
    obtain ⟨hap, hao⟩ := hs a (mem_insert_self a s)
    have ha3 : 3 ≤ a := by
      have := hap.two_le
      rcases hao with ⟨m, hm⟩
      omega
    -- `a ≥ q_{k+1}`
    have haq : qk (s.card + 1) ≤ a := by
      have ha9 : a ≠ 9 := fun h => not_prime_nine (h ▸ hap)
      rcases hao with ⟨m, hm⟩
      rcases ihq with rfl | ⟨b, hb, hbq⟩
      · simp [qk]; omega
      · have hba := hlt b hb
        have hk3 : s.card ≤ 3 := by omega
        have hsc : 1 ≤ s.card := card_pos.mpr ⟨b, hb⟩
        interval_cases hc : s.card <;> simp [qk] at hbq ⊢ <;> omega
    have hxq : xw a ≤ xw (qk (s.card + 1)) := by
      unfold xw
      have hq3 : 3 ≤ qk (s.card + 1) := by
        have : s.card + 1 ≥ 1 := by omega
        rcases s.card with _ | _ | _ | _ | n <;> simp [qk]
      have h1 : (0 : ℚ) < (qk (s.card + 1) : ℚ) - 2 := by
        have : (3 : ℚ) ≤ (qk (s.card + 1) : ℚ) := by exact_mod_cast hq3
        linarith
      apply one_div_le_one_div_of_le h1
      have : (qk (s.card + 1) : ℚ) ≤ a := by exact_mod_cast haq
      linarith
    have hx0 : ∀ i ∈ s, 0 ≤ xw i := by
      intro i hi
      obtain ⟨hip, hio⟩ := hs' i hi
      have : 3 ≤ i := by have := hip.two_le; rcases hio with ⟨m, hm⟩; omega
      unfold xw
      have : (3 : ℚ) ≤ i := by exact_mod_cast this
      apply div_nonneg zero_le_one; linarith
    have hxa0 : 0 ≤ xw a := by
      unfold xw
      have : (3 : ℚ) ≤ a := by exact_mod_cast ha3
      apply div_nonneg zero_le_one; linarith
    have hD0 := bffD_nonneg hx0
    have hS0 : 0 ≤ ∑ p ∈ s, xw p := sum_nonneg hx0
    refine ⟨?_, ?_, Or.inr ⟨a, mem_insert_self a s, haq⟩⟩
    · rw [bffD_insert ha]
      have hbound : (1 + xw a) * bffD s xw + xw a * ∑ i ∈ s, xw i ≤
          (1 + xw (qk (s.card + 1))) * ck s.card + xw (qk (s.card + 1)) * Sk s.card := by
        have e1 : (1 + xw a) * bffD s xw ≤ (1 + xw (qk (s.card + 1))) * ck s.card :=
          mul_le_mul (by linarith) ihD hD0 (by linarith)
        have e2 : xw a * ∑ i ∈ s, xw i ≤ xw (qk (s.card + 1)) * Sk s.card :=
          mul_le_mul hxq ihS hS0 (by linarith)
        linarith
      refine le_trans hbound ?_
      have hk3 : s.card ≤ 3 := by omega
      interval_cases s.card <;> norm_num [qk, ck, Sk, xw]
    · rw [sum_insert ha]
      have hk3 : s.card ≤ 3 := by omega
      have : xw a + ∑ p ∈ s, xw p ≤ xw (qk (s.card + 1)) + Sk s.card := by linarith
      refine le_trans this ?_
      interval_cases s.card <;> norm_num [qk, Sk, xw]

/-- **Five primes are needed.** No covering system with distinct moduli `> 1` has an odd lcm with
at most four distinct prime factors. -/
theorem no_covering_of_card_primeFactors_le_four {L : ℕ} (hL : 0 < L) (hodd : Odd L)
    (h4 : L.primeFactors.card ≤ 4) (S : Finset Cls) : ¬ IsCovering L S := by
  apply no_covering_of_towerSum
  have hs : ∀ p ∈ L.primeFactors, p.Prime ∧ Odd p := by
    intro p hp
    refine ⟨Nat.prime_of_mem_primeFactors hp, ?_⟩
    exact Odd.of_dvd_nat hodd (Nat.dvd_of_mem_primeFactors hp)
  have h := (bff_four_induction L.primeFactors hs h4).1
  have hc : ck L.primeFactors.card < 1 := by
    have : L.primeFactors.card ≤ 4 := h4
    interval_cases L.primeFactors.card <;> norm_num [ck]
  linarith [towerSum_le_bffD hL hodd]

/-- Equivalently: every odd distinct covering system of `ℤ` has at least five distinct primes
dividing the lcm of its moduli. -/
theorem five_primes_of_odd_covering (S : Finset Cls) (hgt : ∀ c ∈ S, 1 < c.d)
    (hodd : ∀ c ∈ S, Odd c.d) (hinj : ∀ c ∈ S, ∀ c' ∈ S, c.d = c'.d → c = c')
    (hcov : CoversZ S) : 5 ≤ (S.lcm (·.d)).primeFactors.card := by
  by_contra hlt
  push_neg at hlt
  have hS := isCovering_lcm S hgt hinj hcov
  have hL := lcm_odd S hodd
  exact no_covering_of_card_primeFactors_le_four hS.pos hL (by omega) S hS

end Covering
