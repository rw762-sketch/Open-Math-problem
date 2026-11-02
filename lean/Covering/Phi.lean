/-
The φ-certificate: a necessary condition for a covering system with distinct moduli
dividing `L`.

Theorem (`one_le_phiSum`). Let `S` be a finite set of classes `r (mod d)` with
`1 < d ∣ L`, pairwise distinct moduli, covering `[0, L)`. Let `P` be the set of primes
dividing `L`. Then
  1 ≤ ∑_{c ∈ S, c.d composite} (1 / c.d) · ∏_{p ∈ P, p ∣ c.d} p / (p − 1).

Consequently, if  ∑_{d ∣ L composite} (1/d) ∏_{p ∣ d} p/(p−1) < 1  (the φ-certificate,
since the summand equals 1/φ(d)), no such covering exists.
-/
import Covering.Basic
import Covering.Count

namespace Covering

open Finset

/-- Classes whose modulus divides `L`, exceeds 1, pairwise distinct moduli, covering `[0,L)`. -/
structure IsCovering (L : ℕ) (S : Finset Cls) : Prop where
  pos : 0 < L
  dvd : ∀ c ∈ S, c.d ∣ L
  gt : ∀ c ∈ S, 1 < c.d
  inj : ∀ c ∈ S, ∀ c' ∈ S, c.d = c'.d → c = c'
  cov : ∀ n, n < L → ∃ c ∈ S, n ≡ c.r [MOD c.d]

/-- Residue function picking, for each modulus `p`, the residue of the class in `S` with that
modulus (or 0 if none). -/
noncomputable def resOf (S : Finset Cls) (p : ℕ) : ℕ :=
  by classical exact
    if h : ∃ c ∈ S, c.d = p then c_choose h |>.r else 0
where c_choose (h : ∃ c ∈ S, c.d = p) : Cls := Classical.choose h

theorem resOf_spec {L : ℕ} {S : Finset Cls} (hS : IsCovering L S) {p : ℕ} {c : Cls}
    (hc : c ∈ S) (hcd : c.d = p) : c.r = resOf S p := by
  classical
  unfold resOf
  have h : ∃ c ∈ S, c.d = p := ⟨c, hc, hcd⟩
  rw [dif_pos h]
  have hspec := Classical.choose_spec h
  have := hS.inj c hc (Classical.choose h) hspec.1 (hcd.trans hspec.2.symm)
  rw [this]
  rfl

/-- Union bound: with `Q` any set of primes dividing `L` (and `a = resOf S`), the avoidance
set is covered by the classes with modulus outside `Q`. -/
theorem card_avoid_le {L : ℕ} {S : Finset Cls} (hS : IsCovering L S) (Q : Finset ℕ) :
    (avoid L Q (resOf S)).card ≤
      ∑ c ∈ S.filter (fun c => c.d ∉ Q), (cls L c.r c.d ∩ avoid L Q (resOf S)).card := by
  classical
  have hsub : avoid L Q (resOf S) ⊆
      (S.filter (fun c => c.d ∉ Q)).biUnion (fun c => cls L c.r c.d ∩ avoid L Q (resOf S)) := by
    intro n hn
    rw [mem_avoid] at hn
    obtain ⟨c, hc, hnc⟩ := hS.cov n hn.1
    rw [mem_biUnion]
    refine ⟨c, ?_, ?_⟩
    · rw [mem_filter]
      refine ⟨hc, fun hcQ => ?_⟩
      have := hn.2 c.d hcQ
      rw [← resOf_spec hS hc rfl] at this
      exact this hnc
    · rw [mem_inter, mem_cls, mem_avoid]
      exact ⟨⟨hn.1, hnc⟩, hn⟩
  exact (card_le_card hsub).trans card_biUnion_le


/-- The summand of the φ-certificate: `(1/d) ∏_{p ∈ P, p ∣ d} p/(p-1)`.  When `P` is the set
of primes dividing `d` this equals `1/φ(d)`. -/
def phiTerm (P : Finset ℕ) (d : ℕ) : ℚ :=
  (1 / (d : ℚ)) * ∏ p ∈ P.filter (· ∣ d), (p : ℚ) / ((p : ℚ) - 1)

theorem avoid_subset_avoid {L : ℕ} {Q Q' : Finset ℕ} {a : ℕ → ℕ} (h : Q' ⊆ Q) :
    avoid L Q a ⊆ avoid L Q' a := by
  intro n hn
  rw [mem_avoid] at *
  exact ⟨hn.1, fun p hp => hn.2 p (h hp)⟩

theorem cls_zero_one (L : ℕ) : cls L 0 1 = range L := by
  ext n; simp [cls, Nat.modEq_one]

/-- Rational form of the product count, for a modulus `d` coprime to `Q`. -/
theorem card_cls_inter_avoid_rat (L : ℕ) (a : ℕ → ℕ) (Q : Finset ℕ)
    (hQp : ∀ p ∈ Q, p.Prime) (hQL : ∀ p ∈ Q, p ∣ L)
    (d r : ℕ) (hd : 0 < d) (hdL : d ∣ L) (hcop : ∀ p ∈ Q, Nat.Coprime p d) :
    ((cls L r d ∩ avoid L Q a).card : ℚ) =
      ((L / d : ℕ) : ℚ) * ∏ p ∈ Q, ((p : ℚ) - 1) / (p : ℚ) := by
  have h := card_cls_inter_avoid L a Q hQp hQL d r hd hdL hcop
  have hpos : ∀ p ∈ Q, (0 : ℚ) < p := fun p hp => by exact_mod_cast (hQp p hp).pos
  have hprod : (0 : ℚ) < ∏ p ∈ Q, (p : ℚ) := prod_pos hpos
  have hcast : ∏ p ∈ Q, ((p - 1 : ℕ) : ℚ) = ∏ p ∈ Q, ((p : ℚ) - 1) :=
    prod_congr rfl (fun p hp => Nat.cast_pred (hQp p hp).pos)
  have h' : ((cls L r d ∩ avoid L Q a).card : ℚ) * ∏ p ∈ Q, (p : ℚ) =
      ((L / d : ℕ) : ℚ) * ∏ p ∈ Q, ((p : ℚ) - 1) := by
    have := congrArg (fun n : ℕ => (n : ℚ)) h
    simp only [Nat.cast_mul, Nat.cast_prod] at this
    rw [hcast] at this
    exact this
  rw [prod_div_distrib, ← mul_div_assoc, eq_div_iff hprod.ne']
  exact h'

/-- **Main inequality.** For a covering `S` of `[0, L)` with distinct moduli `> 1` dividing `L`,
with `P` any set of primes dividing `L` (e.g. all of them, or none):
`1 ≤ ∑_{c ∈ S, c.d ∉ P} phiTerm P c.d`. -/
theorem one_le_phiSum {L : ℕ} {S : Finset Cls} (hS : IsCovering L S) (P : Finset ℕ)
    (hQp : ∀ p ∈ P, p.Prime) (hQL : ∀ p ∈ P, p ∣ L) :
    1 ≤ ∑ c ∈ S.filter (fun c => c.d ∉ P), phiTerm P c.d := by
  classical
  set a := resOf S
  have hp1 : ∀ p ∈ P, (1 : ℚ) < p := fun p hp => by exact_mod_cast (hQp p hp).one_lt
  -- size of the avoidance set
  have hU : ((avoid L P a).card : ℚ) = (L : ℚ) * ∏ p ∈ P, ((p : ℚ) - 1) / (p : ℚ) := by
    have := card_cls_inter_avoid_rat L a P hQp hQL 1 0 Nat.one_pos (one_dvd L)
      (fun p _ => Nat.coprime_one_right p)
    have hsub : avoid L P a ⊆ range L := fun n hn => mem_range.mpr (mem_avoid.mp hn).1
    rw [cls_zero_one, inter_eq_right.mpr hsub] at this
    simpa using this
  set ρ : ℚ := ∏ p ∈ P, ((p : ℚ) - 1) / (p : ℚ) with hρ
  have hρpos : 0 < ρ := prod_pos (fun p hp => div_pos (by linarith [hp1 p hp]) (by linarith [hp1 p hp]))
  have hLpos : (0 : ℚ) < L := by exact_mod_cast hS.pos
  have hW : (0 : ℚ) < (avoid L P a).card := by rw [hU]; positivity
  -- per-class bound: card (cls ∩ U) ≤ card U * phiTerm
  have hterm : ∀ c ∈ S.filter (fun c => c.d ∉ P),
      ((cls L c.r c.d ∩ avoid L P a).card : ℚ) ≤ ((avoid L P a).card : ℚ) * phiTerm P c.d := by
    intro c hc
    rw [mem_filter] at hc
    have hd : 0 < c.d := by have := hS.gt c hc.1; omega
    have hdL : c.d ∣ L := hS.dvd c hc.1
    set Pd := P.filter (fun p => ¬ p ∣ c.d) with hPd
    have hsub : avoid L P a ⊆ avoid L Pd a := avoid_subset_avoid (filter_subset _ _)
    have h1 : (cls L c.r c.d ∩ avoid L P a).card ≤ (cls L c.r c.d ∩ avoid L Pd a).card :=
      card_le_card (inter_subset_inter_left hsub)
    have h2 := card_cls_inter_avoid_rat L a Pd
      (fun p hp => hQp p (mem_filter.mp hp).1) (fun p hp => hQL p (mem_filter.mp hp).1)
      c.d c.r hd hdL (fun p hp => by
        have hp' := mem_filter.mp hp
        exact (Nat.Prime.coprime_iff_not_dvd (hQp p hp'.1)).mpr hp'.2)
    have h1q : ((cls L c.r c.d ∩ avoid L P a).card : ℚ) ≤
        ((L / c.d : ℕ) : ℚ) * ∏ p ∈ Pd, ((p : ℚ) - 1) / (p : ℚ) := by
      rw [← h2]; exact_mod_cast h1
    refine h1q.trans (le_of_eq ?_)
    rw [hU, phiTerm]
    -- split ρ over p ∣ d and p ∤ d
    have hsplit : ρ = (∏ p ∈ P.filter (· ∣ c.d), ((p : ℚ) - 1) / (p : ℚ)) *
        ∏ p ∈ Pd, ((p : ℚ) - 1) / (p : ℚ) := (prod_filter_mul_prod_filter_not P (· ∣ c.d) _).symm
    have hcancel : (∏ p ∈ P.filter (· ∣ c.d), ((p : ℚ) - 1) / (p : ℚ)) *
        ∏ p ∈ P.filter (· ∣ c.d), (p : ℚ) / ((p : ℚ) - 1) = 1 := by
      rw [← prod_mul_distrib]
      refine prod_eq_one (fun p hp => ?_)
      have := hp1 p (mem_filter.mp hp).1
      have hne : (p : ℚ) - 1 ≠ 0 := by linarith
      have hne' : (p : ℚ) ≠ 0 := by linarith
      field_simp
    have hdiv : ((L / c.d : ℕ) : ℚ) = (L : ℚ) / (c.d : ℚ) := by
      rw [Nat.cast_div hdL (by exact_mod_cast hd.ne')]
    rw [hdiv]
    calc (L : ℚ) / c.d * ∏ p ∈ Pd, ((p : ℚ) - 1) / (p : ℚ)
        = (L : ℚ) / c.d * (1 * ∏ p ∈ Pd, ((p : ℚ) - 1) / (p : ℚ)) := by ring
      _ = (L : ℚ) / c.d * ((∏ p ∈ P.filter (· ∣ c.d), ((p : ℚ) - 1) / (p : ℚ)) *
            (∏ p ∈ P.filter (· ∣ c.d), (p : ℚ) / ((p : ℚ) - 1)) *
            ∏ p ∈ Pd, ((p : ℚ) - 1) / (p : ℚ)) := by rw [hcancel]
      _ = (L : ℚ) * ρ * (1 / (c.d : ℚ) * ∏ p ∈ P.filter (· ∣ c.d), (p : ℚ) / ((p : ℚ) - 1)) := by
            rw [hsplit]; ring
  -- sum up
  have hsum := card_avoid_le hS P
  have hsumq : ((avoid L P a).card : ℚ) ≤
      ∑ c ∈ S.filter (fun c => c.d ∉ P), ((cls L c.r c.d ∩ avoid L P a).card : ℚ) := by
    exact_mod_cast hsum
  have hle : ((avoid L P a).card : ℚ) ≤
      ((avoid L P a).card : ℚ) * ∑ c ∈ S.filter (fun c => c.d ∉ P), phiTerm P c.d := by
    rw [mul_sum]
    exact hsumq.trans (sum_le_sum hterm)
  exact (le_mul_iff_one_le_right hW).mp hle

end Covering
