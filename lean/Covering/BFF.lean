/-
The tower certificate sharpens the Berger–Felzenbaum–Fraenkel condition.

For `L` with prime set `P` (all primes `≥ 3`),

  towerSum L ≤ ∏_{p ∈ P} (p−1)/(p−2) − 1 − ∑_{p ∈ P} 1/(p−2).

Proof: each factor of `towerTerm L d` is at most `g p (v_p d)` with `g p 0 = 1` and
`g p v = (p−1)/(p−2) · p^{−v}`; the product `d ↦ ∏_p g p (v_p d)` is multiplicative, so its
sum over the divisors of `L` factors as `∏_p ∑_{v ≤ e_p} g p v = ∏_p (1 + y_p)` with
`y_p = ∑_{1 ≤ v ≤ e_p} g p v ≤ 1/(p−2)`; subtracting the `d = 1` and prime-power terms and
using monotonicity of `∏(1+y) − 1 − ∑ y` in each `y` gives the bound.
-/
import Covering.TowerCheck
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Algebra.Order.Field.GeomSum

namespace Covering

open Finset ArithmeticFunction

/-- Per-prime weight. -/
noncomputable def gw (p v : ℕ) : ℚ :=
  if v = 0 then 1 else ((p : ℚ) - 1) / ((p : ℚ) - 2) * (1 / (p : ℚ)) ^ v

theorem gw_zero (p : ℕ) : gw p 0 = 1 := by simp [gw]

theorem gw_nonneg {p : ℕ} (hp : 3 ≤ p) (v : ℕ) : 0 ≤ gw p v := by
  unfold gw
  split_ifs
  · exact zero_le_one
  · have : (3 : ℚ) ≤ p := by exact_mod_cast hp
    apply mul_nonneg
    · apply div_nonneg <;> linarith
    · positivity

/-! ### The key arithmetic fact about `uu` -/

theorem uu_cast {L p : ℕ} (hp : p.Prime) :
    (uu L p : ℚ) = (p : ℚ) ^ ex L p - ∑ j ∈ range (ex L p), (p : ℚ) ^ j := by
  unfold uu
  rw [Nat.cast_sub (geomSum_lt_pw hp).le]
  push_cast
  rfl

/-- `(p−1)·u_p = (p−2)·p^{e_p} + 1`. -/
theorem uu_identity {L p : ℕ} (hp : p.Prime) :
    ((p : ℚ) - 1) * (uu L p : ℚ) = ((p : ℚ) - 2) * (p : ℚ) ^ ex L p + 1 := by
  rw [uu_cast hp]
  have h := geom_sum_mul (p : ℚ) (ex L p)
  -- h : (∑ i ∈ range n, p ^ i) * (p - 1) = p ^ n - 1
  linear_combination (-1 : ℚ) * h

theorem uu_le_pw (L p : ℕ) : uu L p ≤ pw L p := Nat.sub_le _ _

/-! ### Per-factor bound -/

theorem factor_le_gw {L d p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hdL : ex d p ≤ ex L p) :
    ((min (p ^ (ex L p - ex d p)) (uu L p) : ℕ) : ℚ) / (uu L p : ℚ) ≤ gw p (ex d p) := by
  have hu : (0 : ℚ) < uu L p := by exact_mod_cast uu_pos (L := L) hp
  have hp3q : (3 : ℚ) ≤ p := by exact_mod_cast hp3
  by_cases hv : ex d p = 0
  · rw [hv, gw_zero, Nat.sub_zero]
    have : min (p ^ ex L p) (uu L p) = uu L p := min_eq_right (uu_le_pw L p)
    rw [this, div_self hu.ne']
  · unfold gw
    rw [if_neg hv]
    have hmin : ((min (p ^ (ex L p - ex d p)) (uu L p) : ℕ) : ℚ) ≤ (p : ℚ) ^ (ex L p - ex d p) := by
      exact_mod_cast min_le_left _ _
    calc ((min (p ^ (ex L p - ex d p)) (uu L p) : ℕ) : ℚ) / (uu L p : ℚ)
        ≤ (p : ℚ) ^ (ex L p - ex d p) / (uu L p : ℚ) := by
          exact div_le_div_of_nonneg_right hmin hu.le
      _ ≤ ((p : ℚ) - 1) / ((p : ℚ) - 2) * (1 / (p : ℚ)) ^ ex d p := by
          have hp2q : (0 : ℚ) < (p : ℚ) - 2 := by linarith
          rw [one_div_pow, ← div_eq_mul_one_div, div_div, div_le_div_iff₀ hu (by positivity)]
          have hpow : (p : ℚ) ^ (ex L p - ex d p) * (p : ℚ) ^ ex d p = (p : ℚ) ^ ex L p := by
            rw [← pow_add, Nat.sub_add_cancel hdL]
          have hid := uu_identity (L := L) hp
          calc (p : ℚ) ^ (ex L p - ex d p) * (((p : ℚ) - 2) * (p : ℚ) ^ ex d p)
              = ((p : ℚ) - 2) * (p : ℚ) ^ ex L p := by rw [← hpow]; ring
            _ ≤ ((p : ℚ) - 1) * (uu L p : ℚ) := by rw [hid]; linarith

/-- The multiplicative weight `w d = ∏_{p ∣ d} g p (v_p d)`. -/
noncomputable def wt (d : ℕ) : ℚ := ∏ p ∈ d.primeFactors, gw p (d.factorization p)

theorem wt_one : wt 1 = 1 := by simp [wt]

theorem wt_nonneg {d : ℕ} (hd : Odd d) : 0 ≤ wt d := by
  apply prod_nonneg
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hd) (even_iff_two_dvd.mpr (Nat.dvd_of_mem_primeFactors hp))
  exact gw_nonneg (by have := hpp.two_le; omega) _

theorem towerTerm_le_wt {L d : ℕ} (hL : 0 < L) (hodd : Odd L) (hd : d ∣ L) (hd0 : 0 < d) :
    towerTerm L d ≤ wt d := by
  unfold towerTerm wt
  have hsub : d.primeFactors ⊆ L.primeFactors := Nat.primeFactors_mono hd hL.ne'
  have hfac : ∀ p, d.factorization p ≤ L.factorization p :=
    (Nat.factorization_le_iff_dvd hd0.ne' hL.ne').mpr hd
  rw [prod_subset hsub (f := fun p => gw p (d.factorization p))]
  · apply prod_le_prod
    · intro p _; positivity
    · intro p hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hp2 : p ≠ 2 := by
        rintro rfl
        exact (Nat.not_even_iff_odd.mpr hodd)
          (even_iff_two_dvd.mpr (Nat.dvd_of_mem_primeFactors hp))
      exact factor_le_gw hpp (by have := hpp.two_le; omega) (hfac p)
  · intro p _ hpd
    have : d.factorization p = 0 := Finsupp.notMem_support_iff.mp (by simpa using hpd)
    rw [this, gw_zero]

/-! ### `wt` as a multiplicative arithmetic function -/

noncomputable def wtA : ArithmeticFunction ℚ := ⟨fun d => if d = 0 then 0 else wt d, by simp⟩

theorem wtA_apply {d : ℕ} (hd : d ≠ 0) : wtA d = wt d := by
  show (if d = 0 then 0 else wt d) = wt d
  rw [if_neg hd]

theorem wt_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hmn : m.Coprime n) :
    wt (m * n) = wt m * wt n := by
  unfold wt
  rw [Nat.Coprime.primeFactors_mul hmn, prod_union hmn.disjoint_primeFactors]
  rw [Nat.factorization_mul_of_coprime hmn]
  congr 1
  · apply prod_congr rfl
    intro p hp
    have : n.factorization p = 0 := by
      apply Finsupp.notMem_support_iff.mp
      rw [Nat.support_factorization]
      exact Finset.disjoint_left.mp hmn.disjoint_primeFactors hp
    simp [this]
  · apply prod_congr rfl
    intro p hp
    have : m.factorization p = 0 := by
      apply Finsupp.notMem_support_iff.mp
      rw [Nat.support_factorization]
      exact Finset.disjoint_right.mp hmn.disjoint_primeFactors hp
    simp [this]

theorem wtA_mult : IsMultiplicative wtA := by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨by rw [wtA_apply one_ne_zero, wt_one], ?_⟩
  intro m n hm hn hmn
  rw [wtA_apply (mul_ne_zero hm hn), wtA_apply hm, wtA_apply hn, wt_mul hm hn hmn]

theorem wt_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) : wt (p ^ k) = gw p k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [wt, gw_zero]
  · unfold wt
    rw [Nat.primeFactors_prime_pow hk.ne' hp, prod_singleton, hp.factorization_pow]
    simp

/-- The divisor sum of `wt` factors over primes. -/
theorem sum_divisors_wt {L : ℕ} (hL : 0 < L) :
    ∑ d ∈ L.divisors, wt d = ∏ p ∈ L.primeFactors, ∑ i ∈ range (ex L p + 1), gw p i := by
  have hF : IsMultiplicative ((ζ : ArithmeticFunction ℚ) * wtA) :=
    isMultiplicative_zeta.natCast.mul wtA_mult
  have h1 : ((ζ : ArithmeticFunction ℚ) * wtA) L = ∑ d ∈ L.divisors, wt d := by
    rw [coe_zeta_mul_apply]
    apply sum_congr rfl
    intro d hd
    exact wtA_apply (Nat.pos_of_mem_divisors hd).ne'
  rw [← h1, hF.multiplicative_factorization _ hL.ne', Nat.prod_factorization_eq_prod_primeFactors]
  apply prod_congr rfl
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  rw [coe_zeta_mul_apply, Nat.sum_divisors_prime_pow hpp]
  apply sum_congr rfl
  intro i _
  rw [wtA_apply (pow_ne_zero _ hpp.ne_zero), wt_prime_pow hpp]

/-! ### Geometric bound on the prime-power tail -/

/-- `y_p = ∑_{1 ≤ v ≤ e} g p v`. -/
noncomputable def yw (p e : ℕ) : ℚ := ∑ i ∈ range e, gw p (i + 1)

theorem sum_range_gw (p e : ℕ) : ∑ i ∈ range (e + 1), gw p i = 1 + yw p e := by
  rw [sum_range_succ', gw_zero, yw, add_comm]

theorem yw_nonneg {p : ℕ} (hp : 3 ≤ p) (e : ℕ) : 0 ≤ yw p e :=
  sum_nonneg (fun i _ => gw_nonneg hp _)

theorem yw_le {p : ℕ} (hp : 3 ≤ p) (e : ℕ) : yw p e ≤ 1 / ((p : ℚ) - 2) := by
  have hp3 : (3 : ℚ) ≤ p := by exact_mod_cast hp
  have hpos : (0 : ℚ) < p := by linarith
  have hr0 : (0 : ℚ) ≤ 1 / (p : ℚ) := by positivity
  have hr1 : (1 / (p : ℚ)) < 1 := by rw [div_lt_one hpos]; linarith
  have hgeom : ∑ i ∈ range e, (1 / (p : ℚ)) ^ i ≤ (1 - 1 / (p : ℚ))⁻¹ := by
    have h := geom_sum_Ico_le_of_lt_one hr0 hr1 (m := 0) (n := e)
    rw [← range_eq_Ico, pow_zero] at h
    simpa [one_div] using h
  -- rewrite yw as a geometric sum
  have hyw : yw p e = ((p : ℚ) - 1) / ((p : ℚ) - 2) * (1 / (p : ℚ)) *
      ∑ i ∈ range e, (1 / (p : ℚ)) ^ i := by
    unfold yw gw
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    rw [if_neg (Nat.succ_ne_zero i), pow_succ]
    ring
  rw [hyw]
  have hinv : (1 - 1 / (p : ℚ))⁻¹ = (p : ℚ) / ((p : ℚ) - 1) := by
    field_simp
  rw [hinv] at hgeom
  have hc : (0 : ℚ) < ((p : ℚ) - 1) / ((p : ℚ) - 2) * (1 / (p : ℚ)) := by
    apply mul_pos
    · apply div_pos <;> linarith
    · positivity
  calc ((p : ℚ) - 1) / ((p : ℚ) - 2) * (1 / (p : ℚ)) * ∑ i ∈ range e, (1 / (p : ℚ)) ^ i
      ≤ ((p : ℚ) - 1) / ((p : ℚ) - 2) * (1 / (p : ℚ)) * ((p : ℚ) / ((p : ℚ) - 1)) :=
        mul_le_mul_of_nonneg_left hgeom hc.le
    _ = 1 / ((p : ℚ) - 2) := by
        have h1 : (p : ℚ) - 1 ≠ 0 := by linarith
        have h2 : (p : ℚ) - 2 ≠ 0 := by linarith
        have h3 : (p : ℚ) ≠ 0 := by linarith
        field_simp
        ring

/-! ### Monotonicity of `∏(1+y) − 1 − ∑ y` -/

theorem D_mono (s : Finset ℕ) (x y : ℕ → ℚ) (h0 : ∀ i ∈ s, 0 ≤ y i) (hxy : ∀ i ∈ s, y i ≤ x i) :
    0 ≤ ∏ i ∈ s, (1 + y i) - 1 - ∑ i ∈ s, y i ∧
    ∏ i ∈ s, (1 + y i) - 1 - ∑ i ∈ s, y i ≤ ∏ i ∈ s, (1 + x i) - 1 - ∑ i ∈ s, x i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have h0' : ∀ i ∈ s, 0 ≤ y i := fun i hi => h0 i (mem_insert_of_mem hi)
    have hxy' : ∀ i ∈ s, y i ≤ x i := fun i hi => hxy i (mem_insert_of_mem hi)
    obtain ⟨ih1, ih2⟩ := ih h0' hxy'
    have hya : 0 ≤ y a := h0 a (mem_insert_self a s)
    have hxa : y a ≤ x a := hxy a (mem_insert_self a s)
    have hSy : 0 ≤ ∑ i ∈ s, y i := sum_nonneg h0'
    have hSxy : ∑ i ∈ s, y i ≤ ∑ i ∈ s, x i := sum_le_sum hxy'
    rw [prod_insert ha, prod_insert ha, sum_insert ha, sum_insert ha]
    -- D(insert a s, y) = (1 + y a) * D(s, y) + y a * ∑ y
    have hrec : ∀ z : ℕ → ℚ, (1 + z a) * ∏ i ∈ s, (1 + z i) - 1 - (z a + ∑ i ∈ s, z i) =
        (1 + z a) * (∏ i ∈ s, (1 + z i) - 1 - ∑ i ∈ s, z i) + z a * ∑ i ∈ s, z i := by
      intro z; ring
    rw [hrec y, hrec x]
    constructor
    · positivity
    · have h1 : (1 + y a) * (∏ i ∈ s, (1 + y i) - 1 - ∑ i ∈ s, y i) ≤
          (1 + x a) * (∏ i ∈ s, (1 + x i) - 1 - ∑ i ∈ s, x i) :=
        mul_le_mul (by linarith) ih2 ih1 (by linarith)
      have h2 : y a * ∑ i ∈ s, y i ≤ x a * ∑ i ∈ s, x i :=
        mul_le_mul hxa hSxy hSy (by linarith)
      linarith

/-! ### Assembling the bound -/

/-- The prime powers `p^{i+1}`, `i < e_p`, dividing `L`, and `1`: a subset of the non-composite
divisors. -/
theorem sum_noncomposite_ge {L : ℕ} (hL : 0 < L) (hodd : Odd L) :
    1 + ∑ p ∈ L.primeFactors, yw p (ex L p) ≤
      ∑ d ∈ L.divisors.filter (fun d => ¬ (1 < d ∧ ¬ IsPrimePow d)), wt d := by
  classical
  set Q : Finset ℕ := L.primeFactors.biUnion (fun p => (range (ex L p)).image (fun i => p ^ (i + 1)))
    with hQ
  have hdisj : (L.primeFactors : Set ℕ).PairwiseDisjoint
      (fun p => (range (ex L p)).image (fun i => p ^ (i + 1))) := by
    intro p hp q hq hpq
    rw [Function.onFun, disjoint_left]
    intro n hnp hnq
    rw [mem_image] at hnp hnq
    obtain ⟨i, _, rfl⟩ := hnp
    obtain ⟨j, _, hj⟩ := hnq
    have hpp := Nat.prime_of_mem_primeFactors (Finset.mem_coe.mp hp)
    have hqp := Nat.prime_of_mem_primeFactors (Finset.mem_coe.mp hq)
    have hdvd : q ∣ p ^ (i + 1) := by rw [← hj]; exact dvd_pow_self q (Nat.succ_ne_zero j)
    have := (Nat.prime_dvd_prime_iff_eq hqp hpp).mp (hqp.dvd_of_dvd_pow hdvd)
    exact hpq this.symm
  have hsumQ : ∑ d ∈ Q, wt d = ∑ p ∈ L.primeFactors, yw p (ex L p) := by
    rw [hQ, sum_biUnion hdisj]
    apply sum_congr rfl
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    rw [sum_image]
    · unfold yw
      apply sum_congr rfl
      intro i _
      exact wt_prime_pow hpp (i + 1)
    · intro i _ j _ hij
      have := Nat.pow_right_injective hpp.two_le hij
      omega
  have h1Q : 1 ∉ Q := by
    rw [hQ, mem_biUnion]
    rintro ⟨p, hp, hp1⟩
    rw [mem_image] at hp1
    obtain ⟨i, _, hi⟩ := hp1
    have hpp := Nat.prime_of_mem_primeFactors hp
    have : 2 ≤ p ^ (i + 1) := le_trans hpp.two_le (Nat.le_self_pow (Nat.succ_ne_zero i) p)
    omega
  have hsub : insert 1 Q ⊆ L.divisors.filter (fun d => ¬ (1 < d ∧ ¬ IsPrimePow d)) := by
    intro d hd
    rw [mem_insert] at hd
    rw [mem_filter, Nat.mem_divisors]
    rcases hd with rfl | hd
    · exact ⟨⟨one_dvd _, hL.ne'⟩, by omega⟩
    · rw [hQ, mem_biUnion] at hd
      obtain ⟨p, hp, hd⟩ := hd
      rw [mem_image] at hd
      obtain ⟨i, hi, rfl⟩ := hd
      have hpp := Nat.prime_of_mem_primeFactors hp
      refine ⟨⟨?_, hL.ne'⟩, ?_⟩
      · exact dvd_trans (pow_dvd_pow p (Nat.succ_le_of_lt (mem_range.mp hi))) (Nat.ordProj_dvd L p)
      · intro h
        exact h.2 (hpp.prime.isPrimePow.pow (Nat.succ_ne_zero i))
  calc 1 + ∑ p ∈ L.primeFactors, yw p (ex L p) = ∑ d ∈ insert 1 Q, wt d := by
        rw [sum_insert h1Q, wt_one, hsumQ]
    _ ≤ _ := by
        apply sum_le_sum_of_subset_of_nonneg hsub
        intro d hd _
        rw [mem_filter, Nat.mem_divisors] at hd
        exact wt_nonneg (Odd.of_dvd_nat hodd hd.1.1)

/-- **Tower implies BFF.** -/
theorem towerSum_le_bff {L : ℕ} (hL : 0 < L) (hodd : Odd L) :
    towerSum L ≤ ∏ p ∈ L.primeFactors, ((p : ℚ) - 1) / ((p : ℚ) - 2) - 1 -
      ∑ p ∈ L.primeFactors, 1 / ((p : ℚ) - 2) := by
  classical
  have hp3 : ∀ p ∈ L.primeFactors, 3 ≤ p := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (Nat.dvd_of_mem_primeFactors hp))
    have := hpp.two_le; omega
  -- Step 1: towerSum ≤ sum of wt over composite divisors
  have h1 : towerSum L ≤ ∑ d ∈ L.divisors.filter (fun d => 1 < d ∧ ¬ IsPrimePow d), wt d := by
    unfold towerSum
    apply sum_le_sum
    intro d hd
    rw [mem_filter, Nat.mem_divisors] at hd
    exact towerTerm_le_wt hL hodd hd.1.1 (by omega)
  -- Step 2: split the divisor sum
  have h2 : ∑ d ∈ L.divisors.filter (fun d => 1 < d ∧ ¬ IsPrimePow d), wt d +
      ∑ d ∈ L.divisors.filter (fun d => ¬ (1 < d ∧ ¬ IsPrimePow d)), wt d =
      ∑ d ∈ L.divisors, wt d := sum_filter_add_sum_filter_not _ _ _
  have h3 := sum_noncomposite_ge hL hodd
  have h4 := sum_divisors_wt hL
  have h5 : ∏ p ∈ L.primeFactors, ∑ i ∈ range (ex L p + 1), gw p i =
      ∏ p ∈ L.primeFactors, (1 + yw p (ex L p)) :=
    prod_congr rfl (fun p _ => sum_range_gw p _)
  -- Step 3: monotonicity
  have h6 := D_mono L.primeFactors (fun p => 1 / ((p : ℚ) - 2)) (fun p => yw p (ex L p))
    (fun p hp => yw_nonneg (hp3 p hp) _) (fun p hp => yw_le (hp3 p hp) _)
  have h7 : ∏ p ∈ L.primeFactors, (1 + 1 / ((p : ℚ) - 2)) =
      ∏ p ∈ L.primeFactors, ((p : ℚ) - 1) / ((p : ℚ) - 2) := by
    apply prod_congr rfl
    intro p hp
    have : (3 : ℚ) ≤ p := by exact_mod_cast hp3 p hp
    have h2 : (p : ℚ) - 2 ≠ 0 := by linarith
    field_simp
    ring
  rw [← h7]
  linarith [h6.2]

/-- No covering with an odd lcm whose prime set fails BFF. -/
theorem no_covering_of_bff {L : ℕ} (hL : 0 < L) (hodd : Odd L)
    (h : ∏ p ∈ L.primeFactors, ((p : ℚ) - 1) / ((p : ℚ) - 2) -
      ∑ p ∈ L.primeFactors, 1 / ((p : ℚ) - 2) < 2) (S : Finset Cls) : ¬ IsCovering L S :=
  no_covering_of_towerSum (by linarith [towerSum_le_bff hL hodd]) S

end Covering

namespace Covering

open Finset

/-- **Four-prime theorem** (Hackmon's Theorem 3 at `{3,5,7,11}`): no covering system with distinct
moduli `> 1` has lcm `3^a 5^b 7^c 11^d`, for any exponents `a b c d ≥ 1`. -/
theorem no_covering_3_5_7_11 {a b c d : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (S : Finset Cls) : ¬ IsCovering (3 ^ a * 5 ^ b * 7 ^ c * 11 ^ d) S := by
  have hpf : (3 ^ a * 5 ^ b * 7 ^ c * 11 ^ d).primeFactors = {3, 5, 7, 11} := by
    rw [Nat.primeFactors_mul (by positivity) (by positivity),
      Nat.primeFactors_mul (by positivity) (by positivity),
      Nat.primeFactors_mul (by positivity) (by positivity),
      Nat.primeFactors_pow _ ha.ne', Nat.primeFactors_pow _ hb.ne',
      Nat.primeFactors_pow _ hc.ne', Nat.primeFactors_pow _ hd.ne',
      Nat.Prime.primeFactors (by decide), Nat.Prime.primeFactors (by decide),
      Nat.Prime.primeFactors (by decide), Nat.Prime.primeFactors (by decide)]
    decide
  apply no_covering_of_bff (by positivity)
  · exact Odd.mul (Odd.mul (Odd.mul (Odd.pow (by decide)) (Odd.pow (by decide)))
      (Odd.pow (by decide))) (Odd.pow (by decide))
  · rw [hpf]
    norm_num [prod_insert, sum_insert]

end Covering
