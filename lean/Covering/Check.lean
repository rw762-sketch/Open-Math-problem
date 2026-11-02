/-
Decidable certificates and the bridge from coverings of ℤ to the finite statement.

* `densCheck L`  : ∑_{d ∣ L, d > 1} L/d < L          (the classical density test)
* `phiCheck L`   : ∑_{d ∣ L composite} 1/φ(d) < 1   (the φ-certificate)

Either one, evaluated by the kernel, rules out every covering system with distinct moduli > 1
whose lcm is `L`.
-/
import Covering.Phi
import Covering.Fast
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.BigOperators.Field

namespace Covering

open Finset

/-! ### The two certificates, in kernel-evaluable form -/

/-- Kernel-evaluable φ-sum: a plain list computation (no deduplication). -/
def fastPhiSum (L : ℕ) : ℚ :=
  (((divList L).filter (fun d : ℕ => decide (1 < d ∧ d ∉ primeList L))).map
    (fun d : ℕ => (1 / (d : ℚ)) *
      (((primeList L).filter (fun p : ℕ => decide (p ∣ d))).map
        (fun p : ℕ => (p : ℚ) / ((p : ℚ) - 1))).prod)).sum

/-- Kernel-evaluable density sum `∑_{d ∣ L, d > 1} L / d`. -/
def fastDensSum (L : ℕ) : ℕ :=
  (((divList L).filter (fun d : ℕ => decide (1 < d))).map (fun d : ℕ => L / d)).sum

def phiCheck (L : ℕ) : Bool := decide (fastPhiSum L < 1)
def densCheck (L : ℕ) : Bool := decide (fastDensSum L < L)
def check (L : ℕ) : Bool := densCheck L || phiCheck L

/-- The φ-sum in terms of Mathlib's `Nat.divisors` and `Nat.primeFactors`. -/
def phiSum (L : ℕ) : ℚ :=
  ∑ d ∈ (Nat.divisors L).filter (fun d => 1 < d ∧ d ∉ L.primeFactors), phiTerm L.primeFactors d

theorem phiTerm_eq_list {L d : ℕ} (hL : 0 < L) :
    phiTerm (primeList L).toFinset d =
      (1 / (d : ℚ)) *
        (((primeList L).filter (fun p : ℕ => decide (p ∣ d))).map
          (fun p : ℕ => (p : ℚ) / ((p : ℚ) - 1))).prod := by
  unfold phiTerm
  congr 1
  rw [← List.prod_toFinset _ ((primeList_nodup hL).filter _), List.toFinset_filter]
  simp

theorem phiSum_eq {L : ℕ} (hL : 0 < L) : phiSum L = fastPhiSum L := by
  unfold phiSum fastPhiSum
  rw [divisors_eq_divList hL, primeFactors_eq_primeList hL]
  have hfilt : (divList L).toFinset.filter (fun d => 1 < d ∧ d ∉ (primeList L).toFinset)
      = ((divList L).filter (fun d : ℕ => decide (1 < d ∧ d ∉ primeList L))).toFinset := by
    rw [List.toFinset_filter]
    apply filter_congr
    intro d _
    simp
  rw [hfilt, List.sum_toFinset _ ((divList_nodup hL).filter _)]
  congr 1
  apply List.map_congr_left
  intro d _
  exact phiTerm_eq_list hL

theorem densSum_eq {L : ℕ} (hL : 0 < L) :
    ∑ d ∈ (Nat.divisors L).filter (fun d => 1 < d), L / d = fastDensSum L := by
  unfold fastDensSum
  rw [divisors_eq_divList hL]
  rw [← List.sum_toFinset _ ((divList_nodup hL).filter _), List.toFinset_filter]
  simp

theorem phiTerm_nonneg {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (d : ℕ) : 0 ≤ phiTerm P d := by
  unfold phiTerm
  apply mul_nonneg (by positivity)
  apply prod_nonneg
  intro p hp
  have : (1 : ℚ) < p := by exact_mod_cast (hP p (mem_filter.mp hp).1).one_lt
  apply div_nonneg <;> linarith

/-- Sum over the classes of `S` with modulus in a predicate, rewritten as a sum over moduli. -/
theorem sum_over_moduli {L : ℕ} {S : Finset Cls} (hS : IsCovering L S)
    (q : ℕ → Prop) [DecidablePred q] (f : ℕ → ℚ) :
    ∑ c ∈ S.filter (fun c => q c.d), f c.d = ∑ d ∈ (S.filter (fun c => q c.d)).image (·.d), f d := by
  rw [sum_image]
  intro c hc c' hc' h
  exact hS.inj c (mem_filter.mp hc).1 c' (mem_filter.mp hc').1 h

/-- The φ-certificate excludes `L`. -/
theorem no_covering_of_phiCheck {L : ℕ} (h : phiCheck L = true) (S : Finset Cls) :
    ¬ IsCovering L S := by
  intro hS
  have hL := hS.pos
  have hP : ∀ p ∈ L.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have h1 := one_le_phiSum hS L.primeFactors hP (fun p hp => Nat.dvd_of_mem_primeFactors hp)
  rw [sum_over_moduli hS (fun d => d ∉ L.primeFactors)] at h1
  have hsub : (S.filter (fun c => c.d ∉ L.primeFactors)).image (·.d) ⊆
      (Nat.divisors L).filter (fun d => 1 < d ∧ d ∉ L.primeFactors) := by
    intro d hd
    rw [mem_image] at hd
    obtain ⟨c, hc, rfl⟩ := hd
    rw [mem_filter] at hc ⊢
    exact ⟨Nat.mem_divisors.mpr ⟨hS.dvd c hc.1, hL.ne'⟩, hS.gt c hc.1, hc.2⟩
  have h2 := sum_le_sum_of_subset_of_nonneg hsub
    (fun d _ _ => phiTerm_nonneg hP d)
  have h3 : phiSum L < 1 := by
    rw [phiSum_eq hL]; exact of_decide_eq_true h
  unfold phiSum at h3
  linarith

/-- The density test excludes `L`. -/
theorem no_covering_of_densCheck {L : ℕ} (h : densCheck L = true) (S : Finset Cls) :
    ¬ IsCovering L S := by
  intro hS
  have hL := hS.pos
  have h1 := one_le_phiSum hS ∅ (by simp) (by simp)
  have hfilt : S.filter (fun c => c.d ∉ (∅ : Finset ℕ)) = S := filter_true_of_mem (by simp)
  rw [hfilt] at h1
  have hterm : ∀ c ∈ S, phiTerm ∅ c.d = 1 / (c.d : ℚ) := by
    intro c _; simp [phiTerm]
  rw [sum_congr rfl hterm] at h1
  have hinjS : Set.InjOn (fun c : Cls => c.d) S := fun c hc c' hc' h => hS.inj c hc c' hc' h
  have h1' : ∑ d ∈ S.image (fun c : Cls => c.d), (1 / ((d : ℕ) : ℚ)) =
      ∑ c ∈ S, 1 / ((c.d : ℕ) : ℚ) := sum_image (f := fun d : ℕ => 1 / (d : ℚ)) hinjS
  rw [← h1'] at h1
  have hsub : S.image (fun c : Cls => c.d) ⊆ (Nat.divisors L).filter (fun d => 1 < d) := by
    intro d hd
    rw [mem_image] at hd
    obtain ⟨c, hc, rfl⟩ := hd
    rw [mem_filter]
    exact ⟨Nat.mem_divisors.mpr ⟨hS.dvd c hc, hL.ne'⟩, hS.gt c hc⟩
  have h2 := sum_le_sum_of_subset_of_nonneg (f := fun d : ℕ => 1 / (d : ℚ)) hsub
    (fun d _ _ => by positivity)
  -- the divisor sum equals fastDensSum / L
  have hLq : (0 : ℚ) < L := by exact_mod_cast hL
  have h3 : ∑ d ∈ (Nat.divisors L).filter (fun d => 1 < d), (1 / (d : ℚ)) =
      (fastDensSum L : ℚ) / L := by
    rw [← densSum_eq hL, Nat.cast_sum, Finset.sum_div]
    refine sum_congr rfl (fun d hd => ?_)
    have hdL : d ∣ L := Nat.dvd_of_mem_divisors (mem_filter.mp hd).1
    have hd0 : (d : ℚ) ≠ 0 := by
      have := (mem_filter.mp hd).2; exact_mod_cast (by omega : d ≠ 0)
    rw [Nat.cast_div hdL hd0]
    field_simp
  have h4 : (fastDensSum L : ℚ) < L := by exact_mod_cast (of_decide_eq_true h)
  have h5 : (fastDensSum L : ℚ) / L < 1 := by rwa [div_lt_one hLq]
  linarith

theorem no_covering_of_check {L : ℕ} (h : check L = true) (S : Finset Cls) : ¬ IsCovering L S := by
  unfold check at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact no_covering_of_densCheck h S
  · exact no_covering_of_phiCheck h S

/-! ### From coverings of ℤ to `IsCovering` at the lcm -/

/-- A finite set of classes covers ℤ. -/
def CoversZ (S : Finset Cls) : Prop := ∀ x : ℤ, ∃ c ∈ S, c.mem x

theorem isCovering_lcm (S : Finset Cls) (hgt : ∀ c ∈ S, 1 < c.d)
    (hinj : ∀ c ∈ S, ∀ c' ∈ S, c.d = c'.d → c = c') (hcov : CoversZ S) :
    IsCovering (S.lcm (·.d)) S where
  pos := by
    rcases Nat.eq_zero_or_pos (S.lcm (·.d)) with h | h
    · exfalso
      rw [Finset.lcm_eq_zero_iff] at h
      obtain ⟨c, hc, hc0⟩ := h
      have := hgt c hc
      simp at hc0; omega
    · exact h
  dvd := fun c hc => dvd_lcm hc
  gt := hgt
  inj := hinj
  cov := by
    intro n _
    obtain ⟨c, hc, hmem⟩ := hcov n
    refine ⟨c, hc, ?_⟩
    unfold Cls.mem at hmem
    rw [Nat.modEq_iff_dvd]
    have : ((c.r : ℤ) - (n : ℤ)) = -((n : ℤ) - c.r) := by ring
    rw [this]
    exact (dvd_neg).mpr hmem

theorem lcm_odd (S : Finset Cls) (hodd : ∀ c ∈ S, Odd c.d) : Odd (S.lcm (·.d)) := by
  have hprod : Odd (∏ c ∈ S, c.d) := by
    rw [← Nat.coprime_two_left]
    exact Nat.Coprime.prod_right (fun c hc => Nat.coprime_two_left.mpr (hodd c hc))
  exact hprod.of_dvd_nat (lcm_dvd (fun c hc => dvd_prod_of_mem _ hc))

/-! ### Scanning a block of odd `L` -/

/-- `scanChunk lo cnt = true` iff `check L = true` for every odd `L ∈ (lo, lo + cnt]`. -/
def scanChunk (lo : ℕ) : ℕ → Bool
  | 0 => true
  | cnt + 1 => ((lo + cnt + 1) % 2 == 0 || check (lo + cnt + 1)) && scanChunk lo cnt

theorem scanChunk_spec (lo : ℕ) :
    ∀ cnt, scanChunk lo cnt = true →
      ∀ L, lo < L → L ≤ lo + cnt → L % 2 = 1 → check L = true := by
  intro cnt
  induction cnt with
  | zero => intro _ L h1 h2; omega
  | succ cnt ih =>
    intro h L hlo hle hodd
    unfold scanChunk at h
    rcases Bool.and_eq_true_iff.mp h with ⟨h1, h2⟩
    rcases Nat.lt_or_ge L (lo + cnt + 1) with hlt | hge
    · exact ih h2 L hlo (by omega) hodd
    · have hL : L = lo + cnt + 1 := by omega
      subst hL
      rcases Bool.or_eq_true_iff.mp h1 with h1 | h1
      · exfalso; simp at h1; omega
      · exact h1

theorem scanChunk_append (lo : ℕ) :
    ∀ a b, scanChunk lo a = true → scanChunk (lo + a) b = true → scanChunk lo (a + b) = true := by
  intro a b
  induction b with
  | zero => intro h _; simpa using h
  | succ b ih =>
    intro ha hb
    unfold scanChunk at hb
    rcases Bool.and_eq_true_iff.mp hb with ⟨h1, h2⟩
    have := ih ha h2
    show scanChunk lo (a + b + 1) = true
    unfold scanChunk
    rw [Bool.and_eq_true_iff]
    refine ⟨?_, this⟩
    have e : lo + a + b + 1 = lo + (a + b) + 1 := by omega
    rw [e] at h1
    exact h1

/-- Headline, abstract form: if every odd `L ≤ N` passes `check`, then every covering of ℤ by
finitely many classes with distinct odd moduli `> 1` has lcm `> N`. -/
theorem odd_covering_lcm_gt_of_scan (N : ℕ)
    (hscan : ∀ L, L ≤ N → L % 2 = 1 → check L = true)
    (S : Finset Cls) (hgt : ∀ c ∈ S, 1 < c.d) (hodd : ∀ c ∈ S, Odd c.d)
    (hinj : ∀ c ∈ S, ∀ c' ∈ S, c.d = c'.d → c = c') (hcov : CoversZ S) :
    N < S.lcm (·.d) := by
  by_contra hle
  push_neg at hle
  have hS := isCovering_lcm S hgt hinj hcov
  have hoddL := Nat.odd_iff.mp (lcm_odd S hodd)
  exact no_covering_of_check (hscan _ hle hoddL) S hS

end Covering
