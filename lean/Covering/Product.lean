/-
General CRT product count.

For an index set `I`, pairwise coprime moduli `μ i ∣ L`, and allowed residue sets `S i`,
the residues `n < L` with `n ≡ r (mod d)` and `n % μ i ∈ S i` for all `i` number exactly
`(L / d) · ∏ |S i ∩ range (μ i)| / ∏ μ i`, when `d ∣ L` is coprime to every `μ i`.
-/
import Covering.Count

namespace Covering

open Finset

/-- Residues `n < L` with `n % μ i ∈ S i` for every `i ∈ I`. -/
def prodSet (L : ℕ) (I : Finset ℕ) (μ : ℕ → ℕ) (S : ℕ → Finset ℕ) : Finset ℕ :=
  (range L).filter (fun n => ∀ i ∈ I, n % μ i ∈ S i)

theorem mem_prodSet {L n : ℕ} {I : Finset ℕ} {μ : ℕ → ℕ} {S : ℕ → Finset ℕ} :
    n ∈ prodSet L I μ S ↔ n < L ∧ ∀ i ∈ I, n % μ i ∈ S i := by
  simp [prodSet]

theorem prodSet_empty (L : ℕ) (μ : ℕ → ℕ) (S : ℕ → Finset ℕ) : prodSet L ∅ μ S = range L := by
  ext n; simp [prodSet]

/-- `n % m ∈ S` (with `0 < m`) iff `n ≡ s (mod m)` for some `s ∈ S ∩ range m`. -/
theorem mod_mem_iff {n m : ℕ} (hm : 0 < m) (S : Finset ℕ) :
    n % m ∈ S ↔ ∃ s ∈ S ∩ range m, n ≡ s [MOD m] := by
  constructor
  · intro h
    refine ⟨n % m, mem_inter.mpr ⟨h, mem_range.mpr (Nat.mod_lt n hm)⟩, ?_⟩
    exact (Nat.mod_modEq n m).symm
  · rintro ⟨s, hs, hns⟩
    rw [mem_inter, mem_range] at hs
    have : n % m = s := by
      rw [Nat.ModEq] at hns
      rw [hns, Nat.mod_eq_of_lt hs.2]
    rw [this]; exact hs.1

theorem card_cls_inter_prodSet (L : ℕ) (μ : ℕ → ℕ) (S : ℕ → Finset ℕ) (I : Finset ℕ)
    (hpos : ∀ i ∈ I, 0 < μ i) (hdvd : ∀ i ∈ I, μ i ∣ L)
    (hcop : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Nat.Coprime (μ i) (μ j)) :
    ∀ d r, 0 < d → d ∣ L → (∀ i ∈ I, Nat.Coprime (μ i) d) →
      (cls L r d ∩ prodSet L I μ S).card * ∏ i ∈ I, μ i =
        (L / d) * ∏ i ∈ I, (S i ∩ range (μ i)).card := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    intro d r hd hdL _
    rw [prodSet_empty, prod_empty, prod_empty, mul_one, mul_one]
    rw [inter_eq_left.mpr (fun n hn => mem_range.mpr (mem_cls.mp hn).1), card_cls hd hdL]
  | insert j I hj ih =>
    intro d r hd hdL hcopd
    have hjpos := hpos j (mem_insert_self j I)
    have hjL := hdvd j (mem_insert_self j I)
    have hpos' : ∀ i ∈ I, 0 < μ i := fun i hi => hpos i (mem_insert_of_mem hi)
    have hdvd' : ∀ i ∈ I, μ i ∣ L := fun i hi => hdvd i (mem_insert_of_mem hi)
    have hcop' : ∀ i ∈ I, ∀ k ∈ I, i ≠ k → Nat.Coprime (μ i) (μ k) :=
      fun i hi k hk hik => hcop i (mem_insert_of_mem hi) k (mem_insert_of_mem hk) hik
    have hcopd' : ∀ i ∈ I, Nat.Coprime (μ i) d := fun i hi => hcopd i (mem_insert_of_mem hi)
    have hjd : Nat.Coprime d (μ j) := (hcopd j (mem_insert_self j I)).symm
    have hcopj : ∀ i ∈ I, Nat.Coprime (μ i) (μ j) := fun i hi =>
      hcop i (mem_insert_of_mem hi) j (mem_insert_self j I) (fun h => hj (h ▸ hi))
    have hcop2 : ∀ i ∈ I, Nat.Coprime (μ i) (d * μ j) :=
      fun i hi => Nat.Coprime.mul_right (hcopd' i hi) (hcopj i hi)
    have hdjL : d * μ j ∣ L := Nat.Coprime.mul_dvd_of_dvd_of_dvd hjd hdL hjL
    -- decompose over the allowed residues s mod μ j
    have hdecomp : cls L r d ∩ prodSet L (insert j I) μ S =
        (S j ∩ range (μ j)).biUnion (fun s => cls L r d ∩ cls L s (μ j) ∩ prodSet L I μ S) := by
      ext n
      simp only [mem_inter, mem_cls, mem_prodSet, mem_biUnion, mem_insert, forall_eq_or_imp]
      constructor
      · rintro ⟨⟨hn, hr⟩, _, hj', hI⟩
        obtain ⟨s, hs, hns⟩ := (mod_mem_iff hjpos (S j)).mp hj'
        exact ⟨s, mem_inter.mp hs, ⟨⟨hn, hr⟩, hn, hns⟩, hn, hI⟩
      · rintro ⟨s, hs, ⟨⟨hn, hr⟩, _, hns⟩, _, hI⟩
        exact ⟨⟨hn, hr⟩, hn, (mod_mem_iff hjpos (S j)).mpr ⟨s, mem_inter.mpr hs, hns⟩, hI⟩
    have hdisj : ((S j ∩ range (μ j) : Finset ℕ) : Set ℕ).PairwiseDisjoint
        (fun s => cls L r d ∩ cls L s (μ j) ∩ prodSet L I μ S) := by
      intro s hs t ht hst
      rw [Function.onFun, disjoint_left]
      intro n hn hn'
      simp only [coe_inter, coe_range, Set.mem_inter_iff, Finset.mem_coe, Set.mem_Iio] at hs ht
      simp only [mem_inter, mem_cls] at hn hn'
      apply hst
      have h1 := hn.1.2.2; have h2 := hn'.1.2.2
      have := h1.symm.trans h2
      rw [Nat.ModEq, Nat.mod_eq_of_lt hs.2, Nat.mod_eq_of_lt ht.2] at this
      exact this
    rw [hdecomp, card_biUnion hdisj, prod_insert hj, prod_insert hj]
    -- each piece is a class mod d * μ j intersected with the smaller product set
    have hpiece : ∀ s ∈ S j ∩ range (μ j),
        (cls L r d ∩ cls L s (μ j) ∩ prodSet L I μ S).card * ∏ i ∈ I, μ i =
          (L / (d * μ j)) * ∏ i ∈ I, (S i ∩ range (μ i)).card := by
      intro s _
      obtain ⟨r', hr'⟩ := cls_inter_cls L r d (μ j) s hjd
      rw [hr']
      exact ih hpos' hdvd' hcop' (d * μ j) r' (Nat.mul_pos hd hjpos) hdjL hcop2
    have hk : L / (d * μ j) * μ j = L / d := by
      rw [← Nat.div_div_eq_div_mul]
      exact Nat.div_mul_cancel (Nat.dvd_div_of_mul_dvd hdjL)
    have hsum : ∑ s ∈ S j ∩ range (μ j),
        (cls L r d ∩ cls L s (μ j) ∩ prodSet L I μ S).card * ∏ i ∈ I, μ i =
          (S j ∩ range (μ j)).card * ((L / (d * μ j)) * ∏ i ∈ I, (S i ∩ range (μ i)).card) := by
      rw [sum_congr rfl hpiece, sum_const, smul_eq_mul]
    calc (∑ s ∈ S j ∩ range (μ j), (cls L r d ∩ cls L s (μ j) ∩ prodSet L I μ S).card) *
          (μ j * ∏ i ∈ I, μ i)
        = (∑ s ∈ S j ∩ range (μ j),
            (cls L r d ∩ cls L s (μ j) ∩ prodSet L I μ S).card * ∏ i ∈ I, μ i) * μ j := by
          rw [sum_mul, sum_mul]
          refine sum_congr rfl (fun s _ => by ring)
      _ = (S j ∩ range (μ j)).card * ((L / (d * μ j)) * ∏ i ∈ I, (S i ∩ range (μ i)).card) * μ j := by
          rw [hsum]
      _ = (L / (d * μ j) * μ j) * ((S j ∩ range (μ j)).card * ∏ i ∈ I, (S i ∩ range (μ i)).card) := by
          ring
      _ = L / d * ((S j ∩ range (μ j)).card * ∏ i ∈ I, (S i ∩ range (μ i)).card) := by rw [hk]

end Covering
