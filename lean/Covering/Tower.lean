/-
The tower certificate.

For `L = ∏ p^{e_p}` and a covering with distinct moduli `> 1` dividing `L`, the moduli
`p, p², …, p^{e_p}` are each used at most once; sieving them out leaves, modulo `p^{e_p}`,
at least `u_p = p^{e_p} − (1 + p + ⋯ + p^{e_p − 1})` residues. The remaining classes
(moduli with at least two prime factors) must cover the CRT product of these sets, and a class
modulo `d` meets it in at most `∏_p min(p^{e_p − v_p(d)}, |A_p|)` residues. Hence

  1 ≤ ∑_{d used, ω(d) ≥ 2} ∏_p min(p^{e_p − v_p(d)}, u_p) / u_p.

For squarefree `L` this is the φ-certificate.
-/
import Covering.Product
import Covering.Phi
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Algebra.Order.Ring.GeomSum

namespace Covering

open Finset

/-- Exponent of `p` in `L`. -/
abbrev ex (L p : ℕ) : ℕ := L.factorization p

/-- `p^{e_p}`. -/
abbrev pw (L p : ℕ) : ℕ := p ^ ex L p

/-- `u_p = p^{e_p} − ∑_{j < e_p} p^j`. -/
def uu (L p : ℕ) : ℕ := pw L p - ∑ j ∈ range (ex L p), p ^ j

/-- The tower avoidance set modulo `p^{e_p}`: residues avoiding the class used at each modulus
`p^{e_p − j}`, `j < e_p` (with residue `a (p^{e_p−j})`). -/
def towerAvoid (L p : ℕ) (a : ℕ → ℕ) : Finset ℕ :=
  (range (pw L p)).filter (fun x => ∀ j ∈ range (ex L p),
    ¬ x ≡ a (p ^ (ex L p - j)) [MOD p ^ (ex L p - j)])

theorem geomSum_lt_pw {L p : ℕ} (hp : p.Prime) : ∑ j ∈ range (ex L p), p ^ j < pw L p :=
  Nat.geomSum_lt hp.two_le (fun k hk => mem_range.mp hk)

theorem uu_pos {L p : ℕ} (hp : p.Prime) : 0 < uu L p := by
  unfold uu; have := geomSum_lt_pw (L := L) hp; omega

/-- `|towerAvoid| ≥ u_p`. -/
theorem uu_le_card_towerAvoid {L p : ℕ} (hp : p.Prime) (a : ℕ → ℕ) :
    uu L p ≤ (towerAvoid L p a).card := by
  classical
  let T : Finset ℕ := (range (ex L p)).biUnion
    (fun j => cls (pw L p) (a (p ^ (ex L p - j))) (p ^ (ex L p - j)))
  have hcompl : range (pw L p) \ T ⊆ towerAvoid L p a := by
    intro x hx
    rw [mem_sdiff, mem_biUnion] at hx
    rw [towerAvoid, mem_filter]
    refine ⟨hx.1, fun j hj hxj => hx.2 ⟨j, hj, ?_⟩⟩
    rw [mem_cls]; exact ⟨mem_range.mp hx.1, hxj⟩
  have hT : T.card ≤ ∑ j ∈ range (ex L p), p ^ j := by
    refine card_biUnion_le.trans (sum_le_sum (fun j hj => ?_))
    have hj' := mem_range.mp hj
    have hdvd : p ^ (ex L p - j) ∣ pw L p := pow_dvd_pow p (Nat.sub_le _ j)
    rw [card_cls (Nat.pow_pos hp.pos) hdvd]
    have := Nat.pow_div (Nat.sub_le (ex L p) j) hp.pos (x := p)
    rw [this, Nat.sub_sub_self hj'.le]
  have h1 := card_le_card hcompl
  have h2 := card_sdiff_add_card_inter (range (pw L p)) T
  have h3 : (range (pw L p) ∩ T).card ≤ T.card := card_le_card inter_subset_right
  rw [card_range] at h2
  have h4 : pw L p ≤ (towerAvoid L p a).card + ∑ j ∈ range (ex L p), p ^ j := by
    rw [← h2]; exact Nat.add_le_add h1 (h3.trans hT)
  unfold uu
  exact Nat.sub_le_of_le_add h4

/-- The product set of tower avoidance sets. -/
def towerU (L : ℕ) (a : ℕ → ℕ) : Finset ℕ :=
  prodSet L L.primeFactors (pw L) (fun p => towerAvoid L p a)

theorem prod_pw {L : ℕ} (hL : 0 < L) : ∏ p ∈ L.primeFactors, pw L p = L := by
  have := Nat.factorization_prod_pow_eq_self hL.ne'
  rw [Finsupp.prod, Nat.support_factorization] at this
  exact this

theorem pw_coprime {L p q : ℕ} (hp : p ∈ L.primeFactors) (hq : q ∈ L.primeFactors) (hpq : p ≠ q) :
    Nat.Coprime (pw L p) (pw L q) :=
  (Nat.coprime_pow_primes _ _ (Nat.prime_of_mem_primeFactors hp)
    (Nat.prime_of_mem_primeFactors hq) hpq)

theorem pw_dvd {L p : ℕ} : pw L p ∣ L := Nat.ordProj_dvd L p

theorem pw_pos {L p : ℕ} (hp : p.Prime) : 0 < pw L p := Nat.pow_pos hp.pos

/-- Counting a product set over the prime powers of `L` with `d = 1`. -/
theorem card_prodSet_pw {L : ℕ} (hL : 0 < L) (S : ℕ → Finset ℕ)
    (hS : ∀ p ∈ L.primeFactors, S p ⊆ range (pw L p)) :
    (prodSet L L.primeFactors (pw L) S).card = ∏ p ∈ L.primeFactors, (S p).card := by
  have h := card_cls_inter_prodSet L (pw L) S L.primeFactors
    (fun p hp => pw_pos (Nat.prime_of_mem_primeFactors hp)) (fun _ _ => pw_dvd)
    (fun p hp q hq hpq => pw_coprime hp hq hpq) 1 0 Nat.one_pos (one_dvd L)
    (fun p _ => Nat.coprime_one_right _)
  rw [cls_zero_one, inter_eq_right.mpr (fun n hn => mem_range.mpr (mem_prodSet.mp hn).1),
    prod_pw hL, Nat.div_one] at h
  have h' : (prodSet L L.primeFactors (pw L) S).card * L = L * ∏ p ∈ L.primeFactors, (S p).card := by
    rw [h]
    exact congrArg _ (prod_congr rfl (fun p hp => by rw [inter_eq_left.mpr (hS p hp)]))
  rw [mul_comm] at h'
  exact Nat.eq_of_mul_eq_mul_left hL h'

/-- A class with a modulus that is not a prime power cannot be a tower class. -/
theorem towerU_covered {L : ℕ} {S : Finset Cls} (hS : IsCovering L S) :
    ∀ n ∈ towerU L (resOf S), ∃ c ∈ S, ¬ IsPrimePow c.d ∧ n ≡ c.r [MOD c.d] := by
  intro n hn
  rw [towerU, mem_prodSet] at hn
  obtain ⟨c, hc, hnc⟩ := hS.cov n hn.1
  refine ⟨c, hc, fun hpp => ?_, hnc⟩
  obtain ⟨q, i, hq, hi, hqi⟩ := (isPrimePow_nat_iff c.d).mp hpp
  have hqL : q ∣ L := (dvd_pow_self q hi.ne').trans (hqi ▸ hS.dvd c hc)
  have hqP : q ∈ L.primeFactors := Nat.mem_primeFactors.mpr ⟨hq, hqL, hS.pos.ne'⟩
  have hie : i ≤ ex L q :=
    (hq.pow_dvd_iff_le_factorization hS.pos.ne').mp (hqi ▸ hS.dvd c hc)
  have hA := hn.2 q hqP
  rw [towerAvoid, mem_filter] at hA
  have hj : ex L q - i ∈ range (ex L q) := mem_range.mpr (by omega)
  have := hA.2 (ex L q - i) hj
  rw [show ex L q - (ex L q - i) = i by omega, hqi] at this
  apply this
  rw [← resOf_spec hS hc rfl]
  -- n % q^e ≡ n (mod q^i) since q^i ∣ q^e
  have hdvd : c.d ∣ pw L q := by rw [← hqi]; exact pow_dvd_pow q hie
  exact (Nat.ModEq.of_dvd hdvd (Nat.mod_modEq n (pw L q))).trans hnc

/-- For `c` with `d = c.d ∣ L`, the class meets `U` in at most `∏ min(p^{e−v}, |A_p|)`. -/
theorem card_cls_inter_towerU_le {L : ℕ} {S : Finset Cls} (hS : IsCovering L S) {c : Cls}
    (hc : c ∈ S) :
    (cls L c.r c.d ∩ towerU L (resOf S)).card ≤
      ∏ p ∈ L.primeFactors, min (p ^ (ex L p - ex c.d p)) (towerAvoid L p (resOf S)).card := by
  classical
  have hd : c.d ≠ 0 := by have := hS.gt c hc; omega
  have hdL := hS.dvd c hc
  set a := resOf S
  set S' : ℕ → Finset ℕ := fun p => towerAvoid L p a ∩ cls (pw L p) c.r (p ^ ex c.d p)
  have hsub : cls L c.r c.d ∩ towerU L a ⊆ prodSet L L.primeFactors (pw L) S' := by
    intro n hn
    rw [mem_inter, mem_cls, towerU, mem_prodSet] at hn
    rw [mem_prodSet]
    refine ⟨hn.1.1, fun p hp => ?_⟩
    rw [mem_inter]
    refine ⟨hn.2.2 p hp, ?_⟩
    rw [mem_cls]
    refine ⟨Nat.mod_lt _ (pw_pos (Nat.prime_of_mem_primeFactors hp)), ?_⟩
    have hv : ex c.d p ≤ ex L p := (Nat.factorization_le_iff_dvd hd hS.pos.ne').mpr hdL p
    have h1 : p ^ ex c.d p ∣ c.d := Nat.ordProj_dvd c.d p
    have h2 : p ^ ex c.d p ∣ pw L p := pow_dvd_pow p hv
    exact (Nat.ModEq.of_dvd h2 (Nat.mod_modEq n (pw L p))).trans (Nat.ModEq.of_dvd h1 hn.1.2)
  refine (card_le_card hsub).trans ?_
  rw [card_prodSet_pw hS.pos S' (fun p _ => (inter_subset_left).trans (filter_subset _ _))]
  refine prod_le_prod' (fun p hp => ?_)
  have hp' := Nat.prime_of_mem_primeFactors hp
  have hv : ex c.d p ≤ ex L p := (Nat.factorization_le_iff_dvd hd hS.pos.ne').mpr hdL p
  apply le_min
  · have h2 : p ^ ex c.d p ∣ pw L p := pow_dvd_pow p hv
    have := card_le_card (inter_subset_right (s₁ := towerAvoid L p a) (s₂ := cls (pw L p) c.r (p ^ ex c.d p)))
    rw [card_cls (Nat.pow_pos hp'.pos) h2] at this
    have hq : pw L p / p ^ ex c.d p = p ^ (ex L p - ex c.d p) := Nat.pow_div hv hp'.pos
    rw [hq] at this
    exact this
  · exact card_le_card inter_subset_left

/-- Monotonicity: `min(a, s)/s ≤ min(a, u)/u` for `0 < u ≤ s`. -/
theorem min_div_le_min_div {a u s : ℚ} (ha : 0 ≤ a) (hu : 0 < u) (hus : u ≤ s) :
    min a s / s ≤ min a u / u := by
  have hs : 0 < s := lt_of_lt_of_le hu hus
  rw [← min_div_div_right hs.le, ← min_div_div_right hu.le, div_self hs.ne', div_self hu.ne']
  apply min_le_min_right
  exact div_le_div_of_nonneg_left ha hu hus

/-- **Tower inequality.** -/
theorem one_le_towerSum {L : ℕ} {S : Finset Cls} (hS : IsCovering L S) :
    1 ≤ ∑ c ∈ S.filter (fun c => ¬ IsPrimePow c.d),
      ∏ p ∈ L.primeFactors, ((min (p ^ (ex L p - ex c.d p)) (uu L p) : ℕ) : ℚ) / (uu L p : ℚ) := by
  classical
  set a := resOf S
  set U := towerU L a
  have hprime : ∀ p ∈ L.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  -- |U| = ∏ |A_p|
  have hU : U.card = ∏ p ∈ L.primeFactors, (towerAvoid L p a).card :=
    card_prodSet_pw hS.pos _ (fun p _ => filter_subset _ _)
  have hApos : ∀ p ∈ L.primeFactors, 0 < (towerAvoid L p a).card :=
    fun p hp => lt_of_lt_of_le (uu_pos (hprime p hp)) (uu_le_card_towerAvoid (hprime p hp) a)
  have hUpos : 0 < U.card := by rw [hU]; exact prod_pos hApos
  -- union bound
  have hcov : U ⊆ (S.filter (fun c => ¬ IsPrimePow c.d)).biUnion
      (fun c => cls L c.r c.d ∩ U) := by
    intro n hn
    obtain ⟨c, hc, hpp, hnc⟩ := towerU_covered hS n hn
    rw [mem_biUnion]
    exact ⟨c, mem_filter.mpr ⟨hc, hpp⟩, mem_inter.mpr ⟨mem_cls.mpr ⟨(mem_prodSet.mp hn).1, hnc⟩, hn⟩⟩
  have hsum : U.card ≤ ∑ c ∈ S.filter (fun c => ¬ IsPrimePow c.d), (cls L c.r c.d ∩ U).card :=
    (card_le_card hcov).trans card_biUnion_le
  -- rational bound per class
  have hUq : (0 : ℚ) < U.card := by exact_mod_cast hUpos
  have hterm : ∀ c ∈ S.filter (fun c => ¬ IsPrimePow c.d),
      ((cls L c.r c.d ∩ U).card : ℚ) ≤ (U.card : ℚ) *
        ∏ p ∈ L.primeFactors, ((min (p ^ (ex L p - ex c.d p)) (uu L p) : ℕ) : ℚ) / (uu L p : ℚ) := by
    intro c hc
    have hc' := (mem_filter.mp hc).1
    have h1 := card_cls_inter_towerU_le hS hc'
    have h1q : ((cls L c.r c.d ∩ U).card : ℚ) ≤
        ∏ p ∈ L.primeFactors, ((min (p ^ (ex L p - ex c.d p)) (towerAvoid L p a).card : ℕ) : ℚ) := by
      exact_mod_cast h1
    refine h1q.trans ?_
    rw [hU, Nat.cast_prod, ← prod_mul_distrib]
    refine prod_le_prod (fun p _ => by positivity) (fun p hp => ?_)
    have hp' := hprime p hp
    have hu : (0 : ℚ) < uu L p := by exact_mod_cast uu_pos hp'
    have hs : (uu L p : ℚ) ≤ (towerAvoid L p a).card := by
      exact_mod_cast uu_le_card_towerAvoid hp' a
    have hAq : (0 : ℚ) < (towerAvoid L p a).card := lt_of_lt_of_le hu hs
    set m : ℕ := p ^ (ex L p - ex c.d p)
    rw [Nat.cast_min, Nat.cast_min]
    have key := min_div_le_min_div (a := (m : ℚ)) (by positivity) hu hs
    calc min (m : ℚ) ((towerAvoid L p a).card : ℚ)
        = ((towerAvoid L p a).card : ℚ) * (min (m : ℚ) ((towerAvoid L p a).card : ℚ) /
            ((towerAvoid L p a).card : ℚ)) := by field_simp
      _ ≤ ((towerAvoid L p a).card : ℚ) * (min (m : ℚ) (uu L p : ℚ) / (uu L p : ℚ)) :=
          mul_le_mul_of_nonneg_left key hAq.le
  have hle : (U.card : ℚ) ≤ (U.card : ℚ) * ∑ c ∈ S.filter (fun c => ¬ IsPrimePow c.d),
      ∏ p ∈ L.primeFactors, ((min (p ^ (ex L p - ex c.d p)) (uu L p) : ℕ) : ℚ) / (uu L p : ℚ) := by
    rw [mul_sum]
    calc (U.card : ℚ) ≤ ((∑ c ∈ S.filter (fun c => ¬ IsPrimePow c.d), (cls L c.r c.d ∩ U).card : ℕ) : ℚ) := by
          exact_mod_cast hsum
      _ = ∑ c ∈ S.filter (fun c => ¬ IsPrimePow c.d), ((cls L c.r c.d ∩ U).card : ℚ) := by push_cast; rfl
      _ ≤ _ := sum_le_sum hterm
  exact (le_mul_iff_one_le_right hUq).mp hle

end Covering
