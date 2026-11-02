/-
Fibre decomposition over CRT, and the one-fibre weight of the distorted tower sieve.
-/
import Covering.Tower

namespace Covering.Hybrid

open Finset

/-- Sum over residues mod `a b` = double sum over the CRT coordinates. -/
theorem sum_crt {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) (F : ℕ → ℕ → ℚ) :
    ∑ n ∈ range (a * b), F (n % a) (n % b) = ∑ x ∈ range a, ∑ y ∈ range b, F x y := by
  rw [← Finset.sum_product' (f := F)]
  apply Finset.sum_nbij (fun n => (n % a, n % b))
  · intro n _
    simp only [mem_product, mem_range]
    exact ⟨Nat.mod_lt _ ha, Nat.mod_lt _ hb⟩
  · intro n1 hn1 n2 hn2 h
    simp only [Prod.mk.injEq] at h
    simp only [coe_range, Set.mem_Iio] at hn1 hn2
    have : n1 ≡ n2 [MOD a * b] :=
      (Nat.modEq_and_modEq_iff_modEq_mul hab).mp ⟨h.1, h.2⟩
    rw [Nat.ModEq, Nat.mod_eq_of_lt hn1, Nat.mod_eq_of_lt hn2] at this
    exact this
  · intro ⟨x, y⟩ hxy
    simp only [coe_product, coe_range, Set.mem_prod, Set.mem_Iio] at hxy
    obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hab x y
    refine ⟨k % (a * b), by simpa using Nat.mod_lt _ (Nat.mul_pos ha hb), ?_⟩
    simp only [Prod.mk.injEq]
    constructor
    · rw [Nat.mod_mul_right_mod]; rw [Nat.ModEq] at hk1; rw [hk1, Nat.mod_eq_of_lt hxy.1]
    · rw [Nat.mod_mul_left_mod]; rw [Nat.ModEq] at hk2; rw [hk2, Nat.mod_eq_of_lt hxy.2]
  · intro n _; rfl

/-- A congruence modulo a divisor of `a b` (coprime) splits into the two CRT coordinates. -/
theorem modEq_split_crt {a b m n r : ℕ} (hab : a.Coprime b) (hm : m ∣ a * b) :
    n ≡ r [MOD m] ↔ n % a ≡ r [MOD m.gcd a] ∧ n % b ≡ r [MOD m.gcd b] := by
  have hg : m = m.gcd a * m.gcd b := by
    rw [← Nat.Coprime.gcd_mul m hab, Nat.gcd_eq_left hm]
  have hcop : (m.gcd a).Coprime (m.gcd b) :=
    Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right _ _)
      (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right _ _) hab)
  have h1 : n % a ≡ n [MOD m.gcd a] := (Nat.mod_modEq n a).of_dvd (Nat.gcd_dvd_right _ _)
  have h2 : n % b ≡ n [MOD m.gcd b] := (Nat.mod_modEq n b).of_dvd (Nat.gcd_dvd_right _ _)
  constructor
  · intro h
    exact ⟨h1.trans (h.of_dvd (Nat.gcd_dvd_left _ _)), h2.trans (h.of_dvd (Nat.gcd_dvd_left _ _))⟩
  · rintro ⟨k1, k2⟩
    rw [hg]
    exact (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨h1.symm.trans k1, h2.symm.trans k2⟩

end Covering.Hybrid

namespace Covering.Hybrid

open Finset

/-! ### One fibre -/

section Fibre

variable (A : Finset ℕ) (C : ℕ → Prop) [DecidablePred C] (δ : ℚ)

/-- Fraction of the allowed residues `A` hit by the mixed classes. -/
noncomputable def alpha : ℚ := ((A.filter C).card : ℚ) / A.card

/-- BBMST multipliers on hit and unhit points. -/
noncomputable def kt (α δ : ℚ) : ℚ := if α ≤ δ then 0 else (α - δ) / (α * (1 - δ))
noncomputable def kf (α δ : ℚ) : ℚ := if α ≤ δ then 1 / (1 - α) else 1 / (1 - δ)

/-- The weight on one fibre. -/
noncomputable def wfib (y : ℕ) : ℚ :=
  if y ∈ A then (if C y then kt (alpha A C) δ / A.card else kf (alpha A C) δ / A.card) else 0

/-- Mass of the hit set after distortion. -/
noncomputable def hitMass (α δ : ℚ) : ℚ := if α ≤ δ then 0 else (α - δ) / (1 - δ)

variable {A C δ}

theorem alpha_nonneg : 0 ≤ alpha A C := by unfold alpha; positivity

theorem alpha_le_one (hA : A.Nonempty) : alpha A C ≤ 1 := by
  unfold alpha
  rw [div_le_one (by exact_mod_cast hA.card_pos)]
  exact_mod_cast card_filter_le _ _

theorem kt_nonneg (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2) {α : ℚ} : 0 ≤ kt α δ := by
  unfold kt; split_ifs with h
  · exact le_rfl
  · push_neg at h
    apply div_nonneg (by linarith)
    apply mul_nonneg (by linarith) (by linarith)

theorem kf_nonneg (hδ1 : δ ≤ 1 / 2) {α : ℚ} (hα : α ≤ 1 / 2 ∨ δ < α) : 0 ≤ kf α δ := by
  unfold kf; split_ifs with h
  · apply div_nonneg zero_le_one; linarith
  · apply div_nonneg zero_le_one; linarith

theorem kt_le (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2) {α : ℚ} : kt α δ ≤ 1 / (1 - δ) := by
  unfold kt; split_ifs with h
  · apply div_nonneg zero_le_one; linarith
  · push_neg at h
    have hα : 0 < α := lt_of_le_of_lt hδ0 h
    have h1 : 0 < 1 - δ := by linarith
    rw [div_le_div_iff₀ (mul_pos hα h1) h1]
    nlinarith

theorem kf_le (hδ1 : δ ≤ 1 / 2) {α : ℚ} : kf α δ ≤ 1 / (1 - δ) := by
  unfold kf; split_ifs with h
  · apply one_div_le_one_div_of_le (by linarith); linarith
  · exact le_rfl

theorem kf_nonneg' (hδ1 : δ ≤ 1 / 2) {α : ℚ} : 0 ≤ kf α δ := by
  unfold kf; split_ifs with h
  · apply div_nonneg zero_le_one; linarith
  · apply div_nonneg zero_le_one; linarith

theorem wfib_nonneg (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2) (y : ℕ) : 0 ≤ wfib A C δ y := by
  unfold wfib; split_ifs
  · exact div_nonneg (kt_nonneg hδ0 hδ1) (by positivity)
  · exact div_nonneg (kf_nonneg' hδ1) (by positivity)
  · exact le_rfl

theorem wfib_le (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2) (y : ℕ) :
    wfib A C δ y ≤ if y ∈ A then 1 / (1 - δ) / A.card else 0 := by
  unfold wfib; split_ifs
  · exact div_le_div_of_nonneg_right (kt_le hδ0 hδ1) (by positivity)
  · exact div_le_div_of_nonneg_right (kf_le hδ1) (by positivity)
  · exact le_rfl

/-- Sum of the weight over a set `B` of residues. -/
theorem sum_wfib_le (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2) (B : Finset ℕ) :
    ∑ y ∈ B, wfib A C δ y ≤ 1 / (1 - δ) * ((A ∩ B).card : ℚ) / A.card := by
  calc ∑ y ∈ B, wfib A C δ y ≤ ∑ y ∈ B, (if y ∈ A then 1 / (1 - δ) / A.card else 0) :=
        sum_le_sum (fun y _ => wfib_le hδ0 hδ1 y)
    _ = ∑ y ∈ B.filter (· ∈ A), 1 / (1 - δ) / A.card := by rw [sum_filter]
    _ = ((A ∩ B).card : ℚ) * (1 / (1 - δ) / A.card) := by
        rw [sum_const, nsmul_eq_mul]
        congr 2
        rw [filter_mem_eq_inter, inter_comm]
    _ = 1 / (1 - δ) * ((A ∩ B).card : ℚ) / A.card := by ring

theorem card_split (A : Finset ℕ) (C : ℕ → Prop) [DecidablePred C] :
    ((A.filter C).card : ℚ) + (A.filter (fun y => ¬ C y)).card = A.card := by
  exact_mod_cast filter_card_add_filter_neg_card_eq_card C

theorem sum_over_A {Y : Finset ℕ} (hAY : A ⊆ Y) (F : ℕ → ℚ) :
    ∑ y ∈ Y, (if y ∈ A then F y else 0) = ∑ y ∈ A, F y := by
  rw [← sum_filter, filter_mem_eq_inter, inter_eq_right.mpr hAY]

/-- Total mass of one fibre is `1`. -/
theorem sum_wfib (hA : A.Nonempty) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2) {Y : Finset ℕ} (hAY : A ⊆ Y) :
    ∑ y ∈ Y, wfib A C δ y = 1 := by
  have hc : (0 : ℚ) < A.card := by exact_mod_cast hA.card_pos
  have hsum : ∑ y ∈ Y, wfib A C δ y =
      ((A.filter C).card : ℚ) * (kt (alpha A C) δ / A.card) +
        (A.filter (fun y => ¬ C y)).card * (kf (alpha A C) δ / A.card) := by
    unfold wfib
    rw [sum_over_A hAY, sum_ite, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul]
  rw [hsum]
  have hsplit := card_split A C
  set a := ((A.filter C).card : ℚ)
  set b := ((A.filter (fun y => ¬ C y)).card : ℚ)
  have hα : alpha A C = a / A.card := rfl
  have hb : b = A.card - a := by linarith
  rw [hb]
  unfold kt kf
  rw [hα]
  split_ifs with h
  · have h1 : a < A.card := by
      have : a / A.card < 1 := lt_of_le_of_lt h (by linarith)
      rwa [div_lt_one hc] at this
    have hne : (A.card : ℚ) - a ≠ 0 := by linarith
    have hne2 : (1 : ℚ) - a / A.card ≠ 0 := by
      rw [sub_ne_zero, ne_comm, ne_eq, div_eq_one_iff_eq hc.ne']; linarith
    field_simp
  · push_neg at h
    have ha : 0 < a := by
      have := lt_of_le_of_lt hδ0 h
      rwa [div_pos_iff_of_pos_right hc] at this
    have hd : (1 : ℚ) - δ ≠ 0 := by linarith
    field_simp
    ring

/-- Mass of the hit points of one fibre. -/
theorem sum_wfib_hit (hA : A.Nonempty) {Y : Finset ℕ} (hAY : A ⊆ Y) (hδ0 : 0 ≤ δ) :
    ∑ y ∈ Y.filter C, wfib A C δ y = hitMass (alpha A C) δ := by
  have hc : (0 : ℚ) < A.card := by exact_mod_cast hA.card_pos
  have e1 : ∑ y ∈ Y.filter C, wfib A C δ y = ∑ y ∈ A.filter C, kt (alpha A C) δ / A.card := by
    rw [sum_filter, sum_filter]
    unfold wfib
    rw [← sum_over_A hAY]
    apply sum_congr rfl
    intro y _
    by_cases hy : y ∈ A <;> by_cases hcy : C y <;> simp_all
  rw [e1, sum_const, nsmul_eq_mul]
  have hα : alpha A C = ((A.filter C).card : ℚ) / A.card := rfl
  unfold hitMass kt
  split_ifs with h
  · simp
  · push_neg at h
    have hα0 : 0 < alpha A C := lt_of_le_of_lt hδ0 h
    have hd : (1 : ℚ) - δ ≠ 0 := by
      intro h0; have : δ = 1 := by linarith
      have := alpha_le_one (C := C) hA; linarith
    have : ((A.filter C).card : ℚ) = alpha A C * A.card := by rw [hα, div_mul_cancel₀ _ hc.ne']
    rw [this]
    have hc' : (A.card : ℚ) ≠ 0 := hc.ne'
    field_simp
    ring

/-- The distorted hit mass is at most the first and the (scaled) second moment. -/
theorem hitMass_le (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2) {α : ℚ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    hitMass α δ ≤ α ∧ (0 < δ → hitMass α δ ≤ α ^ 2 / (4 * δ * (1 - δ))) := by
  unfold hitMass
  have hd : 0 < 1 - δ := by linarith
  split_ifs with h
  · exact ⟨hα0, fun hδ => by positivity⟩
  · push_neg at h
    constructor
    · rw [div_le_iff₀ hd]; nlinarith [mul_nonneg hδ0 (sub_nonneg.mpr hα1)]
    · intro hδ
      rw [div_le_div_iff₀ hd (by positivity)]
      nlinarith [sq_nonneg (α - 2 * δ)]

end Fibre

end Covering.Hybrid
