/-
The distorted tower sieve: soundness.

For a list of stages `rs` (reverse exposure order) and a family `S` of classes with distinct
moduli `> 1` dividing `Qs rs`, the weight `Pw rs S` on residues mod `Qs rs` satisfies
  (1) nonnegativity, (2) total mass 1, (3) class bound `P(b mod m) ≤ nu rs m`,
  (4) covered mass `≤ eta rs`.
Consequently a covering forces `1 ≤ eta rs` (`one_le_eta`).
-/
import Covering.Hybrid.Nu
import Mathlib.Algebra.BigOperators.Field

namespace Covering.Hybrid

open Finset Classical

/-- `n` is covered by some class of `S`. -/
def covd (S : Finset Cls) (n : ℕ) : Prop := ∃ c ∈ S, n ≡ c.r [MOD c.d]

/-- Admissible family: moduli divide `Q`, exceed `1`, pairwise distinct. -/
structure Fam (Q : ℕ) (S : Finset Cls) : Prop where
  dvd : ∀ c ∈ S, c.d ∣ Q
  gt : ∀ c ∈ S, 1 < c.d
  inj : ∀ c ∈ S, ∀ c' ∈ S, c.d = c'.d → c = c'

noncomputable def Sold (s : Stage) (S : Finset Cls) : Finset Cls :=
  S.filter (fun c => c.d.Coprime s.p)
noncomputable def Spure (s : Stage) (S : Finset Cls) : Finset Cls :=
  S.filter (fun c => ¬ c.d.Coprime s.p ∧ c.d ∣ s.p ^ s.e)
noncomputable def Smix (s : Stage) (S : Finset Cls) : Finset Cls :=
  S.filter (fun c => ¬ c.d.Coprime s.p ∧ ¬ c.d ∣ s.p ^ s.e)

/-- Residues mod `p^e` missed by the pure classes. -/
noncomputable def Aset (s : Stage) (S : Finset Cls) : Finset ℕ :=
  (range (s.p ^ s.e)).filter (fun y => ∀ c ∈ Spure s S, ¬ y ≡ c.r [MOD c.d])

/-- Fibre point `(x, y)` hit by a mixed class. -/
def Cmix (s : Stage) (Q : ℕ) (S : Finset Cls) (x y : ℕ) : Prop :=
  ∃ c ∈ Smix s S, x ≡ c.r [MOD c.d.gcd Q] ∧ y ≡ c.r [MOD c.d.gcd (s.p ^ s.e)]

noncomputable def Pw : List Stage → Finset Cls → ℕ → ℚ
  | [], _, _ => 1
  | s :: rs, S, n => Pw rs (Sold s S) (n % Qs rs) *
      wfib (Aset s S) (Cmix s (Qs rs) S (n % Qs rs)) s.δ (n % s.p ^ s.e)

/-! ### Splitting a modulus at the newest stage -/

section Split

variable {s : Stage} {rs : List Stage}

/-- Exponent of the stage prime in a modulus. -/
noncomputable def kx (s : Stage) (c : Cls) : ℕ := c.d.factorization s.p

theorem split_mod (hv : Valid (s :: rs)) {d : ℕ} (hd : d ∣ Qs rs * s.p ^ s.e) :
    d = d.gcd (Qs rs) * s.p ^ d.factorization s.p ∧ d.factorization s.p ≤ s.e ∧
      d.gcd (s.p ^ s.e) = s.p ^ d.factorization s.p := by
  obtain ⟨hp, _, _, _, hcop, hv'⟩ := hv
  obtain ⟨v, hve, hdv⟩ := split_dvd (e := s.e) hp hcop hd
  have hQ := Qs_pos rs hv'
  have hg0 : d.gcd (Qs rs) ≠ 0 := (Nat.gcd_pos_of_pos_right _ hQ).ne'
  have hng : ¬ s.p ∣ d.gcd (Qs rs) := fun h =>
    hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop.symm (dvd_trans h (Nat.gcd_dvd_right _ _)))
  have hk : d.factorization s.p = v := by conv_lhs => rw [hdv]; exact fac_mul_pow hp hg0 hng
  rw [hk]
  refine ⟨hdv, hve, ?_⟩
  conv_lhs => rw [hdv]
  rw [Nat.Coprime.gcd_mul_left_cancel _ (Nat.Coprime.pow_right _
      ((Nat.Prime.coprime_iff_not_dvd hp).mpr hng).symm)]
  exact Nat.gcd_eq_left (pow_dvd_pow _ hve)

theorem fam_old (hv : Valid (s :: rs)) {S : Finset Cls} (hS : Fam (Qs (s :: rs)) S) :
    Fam (Qs rs) (Sold s S) := by
  refine ⟨?_, fun c hc => hS.gt c (mem_filter.mp hc).1,
    fun c hc c' hc' h => hS.inj c (mem_filter.mp hc).1 c' (mem_filter.mp hc').1 h⟩
  intro c hc
  obtain ⟨hcS, hcop⟩ := mem_filter.mp hc
  exact Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_right _ hcop) (hS.dvd c hcS)

theorem Aset_sub (S : Finset Cls) : Aset s S ⊆ range (s.p ^ s.e) := filter_subset _ _

/-- `|A| ≥ u`. -/
theorem uS_le_card_Aset (hv : Valid (s :: rs)) {S : Finset Cls} (hS : Fam (Qs (s :: rs)) S) :
    uS s ≤ (Aset s S).card := by
  obtain ⟨hp, he, _, _, hcop, hv'⟩ := hv
  have hvv : Valid (s :: rs) := ⟨hp, he, ‹_›, ‹_›, hcop, hv'⟩
  set f := s.p ^ s.e
  let T : Finset ℕ := (Spure s S).biUnion (fun c => cls f c.r c.d)
  have hcompl : range f \ T ⊆ Aset s S := by
    intro y hy
    rw [mem_sdiff, mem_biUnion] at hy
    refine mem_filter.mpr ⟨hy.1, fun c hc hyc => hy.2 ⟨c, hc, mem_cls.mpr ⟨mem_range.mp hy.1, hyc⟩⟩⟩
  -- each pure modulus is p^k with 1 ≤ k ≤ e, and distinct moduli give distinct k
  have hpure : ∀ c ∈ Spure s S, c.d = s.p ^ kx s c ∧ 1 ≤ kx s c ∧ kx s c ≤ s.e := by
    intro c hc
    obtain ⟨hcS, hnc, hcf⟩ := mem_filter.mp hc
    obtain ⟨k, hk, hck⟩ := (Nat.dvd_prime_pow hp).mp hcf
    have hk' : kx s c = k := by unfold kx; rw [hck, hp.factorization_pow]; simp
    refine ⟨by rw [hk']; exact hck, ?_, by rw [hk']; exact hk⟩
    rw [hk']
    by_contra h0
    push_neg at h0
    have : k = 0 := by omega
    rw [this, pow_zero] at hck
    exact absurd (hS.gt c hcS) (by omega)
  have hT : T.card ≤ ∑ j ∈ range s.e, s.p ^ j := by
    refine card_biUnion_le.trans ?_
    have h1 : ∀ c ∈ Spure s S, (cls f c.r c.d).card = s.p ^ (s.e - kx s c) := by
      intro c hc
      obtain ⟨hcd, _, hke⟩ := hpure c hc
      rw [card_cls (by rw [hcd]; exact pow_pos hp.pos _) (by rw [hcd]; exact pow_dvd_pow _ hke), hcd]
      exact Nat.pow_div hke hp.pos
    rw [sum_congr rfl h1]
    have hinj : Set.InjOn (fun c => s.e - kx s c) (Spure s S) := by
      intro c hc c' hc' h
      simp only at h
      obtain ⟨hcd, hk1, hke⟩ := hpure c hc
      obtain ⟨hcd', hk1', hke'⟩ := hpure c' hc'
      have : kx s c = kx s c' := by omega
      exact hS.inj c (mem_filter.mp hc).1 c' (mem_filter.mp hc').1 (by rw [hcd, hcd', this])
    rw [← sum_image (f := fun j => s.p ^ j) hinj]
    apply sum_le_sum_of_subset_of_nonneg
    · intro j hj
      obtain ⟨c, hc, rfl⟩ := mem_image.mp hj
      have := (hpure c hc).2.1
      exact mem_range.mpr (by omega)
    · intro _ _ _; positivity
  have h1 := card_le_card hcompl
  have h2 := card_sdiff_add_card_inter (range f) T
  have h3 : (range f ∩ T).card ≤ T.card := card_le_card inter_subset_right
  rw [card_range] at h2
  unfold uS
  omega

theorem Aset_nonempty (hv : Valid (s :: rs)) {S : Finset Cls} (hS : Fam (Qs (s :: rs)) S) :
    (Aset s S).Nonempty := by
  apply card_pos.mp
  exact lt_of_lt_of_le (uS_pos hv.1) (uS_le_card_Aset hv hS)

end Split

/-! ### One stage: mass and class bound -/

section Step

variable {s : Stage} {rs : List Stage} {S : Finset Cls}

theorem Pw_cons (n : ℕ) : Pw (s :: rs) S n = Pw rs (Sold s S) (n % Qs rs) *
    wfib (Aset s S) (Cmix s (Qs rs) S (n % Qs rs)) s.δ (n % s.p ^ s.e) := rfl

theorem Pw_cons_nonneg (hv : Valid (s :: rs)) (hP : ∀ x, 0 ≤ Pw rs (Sold s S) x) (n : ℕ) :
    0 ≤ Pw (s :: rs) S n :=
  mul_nonneg (hP _) (wfib_nonneg hv.2.2.1 hv.2.2.2.1 _)

/-- Sum over residues mod `Q p^e` of a function of the two coordinates. -/
theorem sum_cons (hv : Valid (s :: rs)) (F : ℕ → ℕ → ℚ) :
    ∑ n ∈ range (Qs (s :: rs)), F (n % Qs rs) (n % s.p ^ s.e) =
      ∑ x ∈ range (Qs rs), ∑ y ∈ range (s.p ^ s.e), F x y :=
  sum_crt (Qs_pos rs hv.2.2.2.2.2) (pow_pos hv.1.pos _) (hv.2.2.2.2.1.pow_right _) F

theorem Pw_cons_mass (hv : Valid (s :: rs)) (hS : Fam (Qs (s :: rs)) S)
    (hmass : ∑ x ∈ range (Qs rs), Pw rs (Sold s S) x = 1) :
    ∑ n ∈ range (Qs (s :: rs)), Pw (s :: rs) S n = 1 := by
  refine (sum_cons hv (fun x y => Pw rs (Sold s S) x *
        wfib (Aset s S) (Cmix s (Qs rs) S x) s.δ y)).trans ?_
  simp only [← mul_sum]
  rw [← hmass]
  apply sum_congr rfl
  intro x _
  rw [sum_wfib (Aset_nonempty hv hS) hv.2.2.1 hv.2.2.2.1 (Aset_sub S), mul_one]

/-- Inner fibre bound for the class `b (mod p^k)`. -/
theorem fibre_class_le (hv : Valid (s :: rs)) (hS : Fam (Qs (s :: rs)) S) (x b k : ℕ)
    (hk : k ≤ s.e) :
    ∑ y ∈ range (s.p ^ s.e), (if y ≡ b [MOD s.p ^ k] then
      wfib (Aset s S) (Cmix s (Qs rs) S x) s.δ y else 0) ≤ γS s k := by
  obtain ⟨hp, he, hd0, hd1, hcop, hv'⟩ := hv
  have hvv : Valid (s :: rs) := ⟨hp, he, hd0, hd1, hcop, hv'⟩
  have hA := Aset_nonempty hvv hS
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp only [pow_zero, Nat.modEq_one, if_true]
    rw [sum_wfib hA hd0 hd1 (Aset_sub S)]
    simp [γS]
  · rw [← sum_filter]
    have hB := sum_wfib_le (A := Aset s S) (C := Cmix s (Qs rs) S x) hd0 hd1
      ((range (s.p ^ s.e)).filter (fun y => y ≡ b [MOD s.p ^ k]))
    refine hB.trans ?_
    have hcard : ((Aset s S ∩ (range (s.p ^ s.e)).filter (fun y => y ≡ b [MOD s.p ^ k])).card : ℚ)
        ≤ ((min (s.p ^ (s.e - k)) (Aset s S).card : ℕ) : ℚ) := by
      have h1 : (Aset s S ∩ (range (s.p ^ s.e)).filter (fun y => y ≡ b [MOD s.p ^ k])).card
          ≤ s.p ^ (s.e - k) := by
        refine (card_le_card inter_subset_right).trans ?_
        have := card_cls (L := s.p ^ s.e) (r := b) (pow_pos hp.pos k) (pow_dvd_pow _ hk)
        rw [cls, Nat.pow_div hk hp.pos] at this
        rw [this]
      have h2 := card_le_card (inter_subset_left (s₁ := Aset s S)
        (s₂ := (range (s.p ^ s.e)).filter (fun y => y ≡ b [MOD s.p ^ k])))
      exact_mod_cast le_min h1 h2
    have hcA : (0 : ℚ) < (Aset s S).card := by exact_mod_cast hA.card_pos
    have huA : ((uS s : ℕ) : ℚ) ≤ (Aset s S).card := by exact_mod_cast uS_le_card_Aset hvv hS
    have hu0 : (0 : ℚ) < uS s := by exact_mod_cast uS_pos hp
    have hmin := min_div_le_min_div (a := ((s.p ^ (s.e - k) : ℕ) : ℚ)) (by positivity) hu0 huA
    unfold γS
    rw [if_neg (by omega)]
    unfold gS cS
    push_cast at hcard hmin ⊢
    calc 1 / (1 - s.δ) * ((Aset s S ∩ (range (s.p ^ s.e)).filter
            (fun y => y ≡ b [MOD s.p ^ k])).card : ℚ) / (Aset s S).card
        ≤ 1 / (1 - s.δ) * (min ((s.p : ℚ) ^ (s.e - k)) ((Aset s S).card : ℚ)) / (Aset s S).card := by
          apply div_le_div_of_nonneg_right _ hcA.le
          apply mul_le_mul_of_nonneg_left hcard
          apply div_nonneg zero_le_one; linarith
      _ = 1 / (1 - s.δ) * (min ((s.p : ℚ) ^ (s.e - k)) ((Aset s S).card : ℚ) / (Aset s S).card) := by
          ring
      _ ≤ 1 / (1 - s.δ) * (min ((s.p : ℚ) ^ (s.e - k)) (uS s : ℚ) / uS s) := by
          apply mul_le_mul_of_nonneg_left hmin
          apply div_nonneg zero_le_one; linarith

/-- Class bound for the new stage. -/
theorem Pw_cons_class (hv : Valid (s :: rs)) (hS : Fam (Qs (s :: rs)) S)
    (hP : ∀ x, 0 ≤ Pw rs (Sold s S) x)
    (hcls : ∀ m b, m ∣ Qs rs →
      ∑ x ∈ (range (Qs rs)).filter (fun x => x ≡ b [MOD m]), Pw rs (Sold s S) x ≤ nu rs m)
    (m b : ℕ) (hm : m ∣ Qs (s :: rs)) :
    ∑ n ∈ (range (Qs (s :: rs))).filter (fun n => n ≡ b [MOD m]), Pw (s :: rs) S n ≤
      nu (s :: rs) m := by
  have hcop : (Qs rs).Coprime (s.p ^ s.e) := hv.2.2.2.2.1.pow_right _
  obtain ⟨hdec, hke, hgf⟩ := split_mod hv hm
  set k := m.factorization s.p
  set m1 := m.gcd (Qs rs)
  rw [sum_filter]
  have hpt : ∀ n ∈ range (Qs (s :: rs)), (if n ≡ b [MOD m] then Pw (s :: rs) S n else 0) =
      (fun x y => if x ≡ b [MOD m1] then Pw rs (Sold s S) x *
        (if y ≡ b [MOD s.p ^ k] then wfib (Aset s S) (Cmix s (Qs rs) S x) s.δ y else 0) else 0)
        (n % Qs rs) (n % s.p ^ s.e) := by
    intro n _
    have hiff : n ≡ b [MOD m] ↔ n % Qs rs ≡ b [MOD m1] ∧ n % s.p ^ s.e ≡ b [MOD s.p ^ k] := by
      rw [← hgf]; exact modEq_split_crt hcop hm
    rw [Pw_cons]
    by_cases h1 : n % Qs rs ≡ b [MOD m1] <;> by_cases h2 : n % s.p ^ s.e ≡ b [MOD s.p ^ k] <;>
      simp [hiff, h1, h2]
  rw [sum_congr rfl hpt]
  refine (sum_cons hv (fun x y => if x ≡ b [MOD m1] then Pw rs (Sold s S) x *
        (if y ≡ b [MOD s.p ^ k] then wfib (Aset s S) (Cmix s (Qs rs) S x) s.δ y else 0)
        else 0)).trans_le ?_
  calc ∑ x ∈ range (Qs rs), ∑ y ∈ range (s.p ^ s.e), (if x ≡ b [MOD m1] then Pw rs (Sold s S) x *
        (if y ≡ b [MOD s.p ^ k] then wfib (Aset s S) (Cmix s (Qs rs) S x) s.δ y else 0) else 0)
      ≤ ∑ x ∈ range (Qs rs), (if x ≡ b [MOD m1] then Pw rs (Sold s S) x * γS s k else 0) := by
        apply sum_le_sum
        intro x _
        split_ifs with hx
        · rw [← mul_sum]
          exact mul_le_mul_of_nonneg_left (fibre_class_le hv hS x b k hke) (hP x)
        · simp
    _ = γS s k * ∑ x ∈ (range (Qs rs)).filter (fun x => x ≡ b [MOD m1]), Pw rs (Sold s S) x := by
        rw [sum_filter, mul_sum]
        apply sum_congr rfl; intro x _; split_ifs <;> ring
    _ ≤ γS s k * nu rs m1 :=
        mul_le_mul_of_nonneg_left (hcls m1 b (Nat.gcd_dvd_right _ _)) (γS_nonneg hv.2.2.2.1 k)
    _ = nu (s :: rs) m := by
        conv_rhs => rw [hdec]
        rw [nu_cons_mul_pow hv (Nat.gcd_dvd_right _ _), mul_comm]

/-- Fraction of the allowed residues in one class modulo `p^k`. -/
theorem inter_cls_le (hv : Valid (s :: rs)) (hS : Fam (Qs (s :: rs)) S) (r k : ℕ) (hk : k ≤ s.e) :
    ((Aset s S ∩ cls (s.p ^ s.e) r (s.p ^ k)).card : ℚ) / (Aset s S).card ≤ gS s k := by
  have hp := hv.1
  have hA := Aset_nonempty hv hS
  have hcard : ((Aset s S ∩ cls (s.p ^ s.e) r (s.p ^ k)).card : ℚ)
      ≤ ((min (s.p ^ (s.e - k)) (Aset s S).card : ℕ) : ℚ) := by
    have h1 : (Aset s S ∩ cls (s.p ^ s.e) r (s.p ^ k)).card ≤ s.p ^ (s.e - k) := by
      refine (card_le_card inter_subset_right).trans ?_
      rw [card_cls (pow_pos hp.pos k) (pow_dvd_pow _ hk), Nat.pow_div hk hp.pos]
    exact_mod_cast le_min h1 (card_le_card inter_subset_left)
  have hcA : (0 : ℚ) < (Aset s S).card := by exact_mod_cast hA.card_pos
  have huA : ((uS s : ℕ) : ℚ) ≤ (Aset s S).card := by exact_mod_cast uS_le_card_Aset hv hS
  have hu0 : (0 : ℚ) < uS s := by exact_mod_cast uS_pos hp
  have hmin := min_div_le_min_div (a := ((s.p ^ (s.e - k) : ℕ) : ℚ)) (by positivity) hu0 huA
  unfold gS
  push_cast at hcard hmin ⊢
  exact (div_le_div_of_nonneg_right hcard hcA.le).trans hmin

end Step

/-! ### One stage: covered mass -/

section Cover

variable {s : Stage} {rs : List Stage} {S : Finset Cls}

theorem mem_cases (c : Cls) (hc : c ∈ S) :
    c ∈ Sold s S ∨ c ∈ Spure s S ∨ c ∈ Smix s S := by
  unfold Sold Spure Smix
  simp only [mem_filter]
  by_cases h1 : c.d.Coprime s.p
  · exact Or.inl ⟨hc, h1⟩
  · by_cases h2 : c.d ∣ s.p ^ s.e
    · exact Or.inr (Or.inl ⟨hc, h1, h2⟩)
    · exact Or.inr (Or.inr ⟨hc, h1, h2⟩)

theorem covd_split (hv : Valid (s :: rs)) (hS : Fam (Qs (s :: rs)) S) {n : ℕ} (h : covd S n) :
    covd (Sold s S) (n % Qs rs) ∨ n % s.p ^ s.e ∉ Aset s S ∨
      Cmix s (Qs rs) S (n % Qs rs) (n % s.p ^ s.e) := by
  obtain ⟨c, hc, hnc⟩ := h
  have hcop : (Qs rs).Coprime (s.p ^ s.e) := hv.2.2.2.2.1.pow_right _
  rcases mem_cases (s := s) c hc with h1 | h1 | h1
  · left
    have hdQ := (fam_old hv hS).dvd c h1
    exact ⟨c, h1, ((Nat.mod_modEq n _).of_dvd hdQ).trans hnc⟩
  · right; left
    intro hA
    have hdf := (mem_filter.mp h1).2.2
    exact (mem_filter.mp hA).2 c h1 (((Nat.mod_modEq n _).of_dvd hdf).trans hnc)
  · right; right
    exact ⟨c, h1, (modEq_split_crt hcop (hS.dvd c hc)).mp hnc⟩

/-- Mixed classes are determined by `(gcd(d, Q), k)`, with `gcd ≠ 1` and `1 ≤ k ≤ e`. -/
theorem mix_key (hv : Valid (s :: rs)) (hS : Fam (Qs (s :: rs)) S) {c : Cls} (hc : c ∈ Smix s S) :
    c.d.gcd (Qs rs) ∈ (Qs rs).divisors.erase 1 ∧ kx s c ∈ Icc 1 s.e := by
  obtain ⟨hcS, hnc, hnf⟩ := mem_filter.mp hc
  obtain ⟨hdec, hke, hgf⟩ := split_mod hv (hS.dvd c hcS)
  have hQ := Qs_pos rs hv.2.2.2.2.2
  refine ⟨?_, ?_⟩
  · rw [mem_erase, Nat.mem_divisors]
    refine ⟨fun h1 => ?_, Nat.gcd_dvd_right _ _, hQ.ne'⟩
    rw [h1, one_mul] at hdec
    exact hnf (by rw [hdec]; exact pow_dvd_pow _ hke)
  · rw [mem_Icc]
    refine ⟨?_, hke⟩
    by_contra h0
    push_neg at h0
    have : kx s c = 0 := by omega
    unfold kx at this
    rw [this, pow_zero, mul_one] at hdec
    apply hnc
    rw [hdec]
    exact Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right _ _) hv.2.2.2.2.1

theorem mix_sum_le (hv : Valid (s :: rs)) (hS : Fam (Qs (s :: rs)) S) (F : ℕ → ℕ → ℚ)
    (hF : ∀ m j, 0 ≤ F m j) :
    ∑ c ∈ Smix s S, F (c.d.gcd (Qs rs)) (kx s c) ≤
      ∑ m ∈ (Qs rs).divisors.erase 1, ∑ j ∈ Icc 1 s.e, F m j := by
  rw [← sum_product' (f := F)]
  have hinj : Set.InjOn (fun c : Cls => (c.d.gcd (Qs rs), kx s c)) (Smix s S) := by
    intro c hc c' hc' h
    simp only [Prod.mk.injEq] at h
    have hcS := (mem_filter.mp hc).1
    have hcS' := (mem_filter.mp hc').1
    have e1 := (split_mod hv (hS.dvd c hcS)).1
    have e2 := (split_mod hv (hS.dvd c' hcS')).1
    apply hS.inj c hcS c' hcS'
    rw [e1, e2, h.1]
    unfold kx at h
    rw [h.2]
  rw [← sum_image (f := fun t : ℕ × ℕ => F t.1 t.2) hinj]
  apply sum_le_sum_of_subset_of_nonneg
  · intro t ht
    obtain ⟨c, hc, rfl⟩ := mem_image.mp ht
    obtain ⟨h1, h2⟩ := mix_key hv hS hc
    exact mem_product.mpr ⟨h1, h2⟩
  · intro t _ _; exact hF _ _

theorem sum_nu_erase (hv : Valid rs) : ∑ m ∈ (Qs rs).divisors.erase 1, nu rs m = Pi1 rs - 1 := by
  rw [sum_erase_eq_sub (Nat.mem_divisors.mpr ⟨one_dvd _, (Qs_pos rs hv).ne'⟩), sum_nu rs hv,
    nu_one]

theorem sum_nu2_erase (hv : Valid rs) :
    ∑ m ∈ (Qs rs).divisors.erase 1, ∑ m' ∈ (Qs rs).divisors.erase 1, nu rs (m.lcm m') =
      Pi2 rs - 2 * Pi1 rs + 1 := by
  have h1 : (1 : ℕ) ∈ (Qs rs).divisors := Nat.mem_divisors.mpr ⟨one_dvd _, (Qs_pos rs hv).ne'⟩
  have hD := insert_erase h1
  have htot := sum_nu2 rs hv
  rw [← hD] at htot
  simp only [sum_insert (Finset.notMem_erase 1 _), Nat.lcm_one_left, Nat.lcm_one_right] at htot
  rw [sum_add_distrib, nu_one, sum_nu_erase hv] at htot
  linarith

/-- `α(x) ≤ Σ_{mixed c, x ≡ c.r (mod gcd)} g(k_c)`. -/
theorem alpha_le_sum (hv : Valid (s :: rs)) (hS : Fam (Qs (s :: rs)) S) (x : ℕ) :
    alpha (Aset s S) (Cmix s (Qs rs) S x) ≤
      ∑ c ∈ Smix s S, (if x ≡ c.r [MOD c.d.gcd (Qs rs)] then gS s (kx s c) else 0) := by
  have hA := Aset_nonempty hv hS
  have hcA : (0 : ℚ) < (Aset s S).card := by exact_mod_cast hA.card_pos
  set T := (Smix s S).filter (fun c => x ≡ c.r [MOD c.d.gcd (Qs rs)])
  have hsub : (Aset s S).filter (Cmix s (Qs rs) S x) ⊆
      T.biUnion (fun c => Aset s S ∩ cls (s.p ^ s.e) c.r (s.p ^ kx s c)) := by
    intro y hy
    obtain ⟨hyA, c, hc, hx, hy'⟩ := mem_filter.mp hy
    rw [mem_biUnion]
    refine ⟨c, mem_filter.mpr ⟨hc, hx⟩, mem_inter.mpr ⟨hyA, mem_cls.mpr ⟨?_, ?_⟩⟩⟩
    · exact mem_range.mp (Aset_sub S hyA)
    · have := (split_mod hv (hS.dvd c (mem_filter.mp hc).1)).2.2
      rw [this] at hy'; exact hy'
  unfold alpha
  calc ((((Aset s S).filter (Cmix s (Qs rs) S x)).card : ℕ) : ℚ) / (Aset s S).card
      ≤ (∑ c ∈ T, ((Aset s S ∩ cls (s.p ^ s.e) c.r (s.p ^ kx s c)).card : ℚ)) / (Aset s S).card := by
        apply div_le_div_of_nonneg_right _ hcA.le
        exact_mod_cast (card_le_card hsub).trans card_biUnion_le
    _ = ∑ c ∈ T, ((Aset s S ∩ cls (s.p ^ s.e) c.r (s.p ^ kx s c)).card : ℚ) / (Aset s S).card := by
        rw [sum_div]
    _ ≤ ∑ c ∈ T, gS s (kx s c) := by
        apply sum_le_sum
        intro c hc
        exact inter_cls_le hv hS c.r (kx s c)
          (split_mod hv (hS.dvd c (mem_filter.mp (mem_filter.mp hc).1).1)).2.1
    _ = ∑ c ∈ Smix s S, (if x ≡ c.r [MOD c.d.gcd (Qs rs)] then gS s (kx s c) else 0) := by
        rw [sum_filter]

section Moments

variable (hv : Valid (s :: rs)) (hS : Fam (Qs (s :: rs)) S)
  (hP : ∀ x, 0 ≤ Pw rs (Sold s S) x)
  (hcls : ∀ m b, m ∣ Qs rs →
    ∑ x ∈ (range (Qs rs)).filter (fun x => x ≡ b [MOD m]), Pw rs (Sold s S) x ≤ nu rs m)
include hv hS hP hcls

theorem first_moment :
    ∑ x ∈ range (Qs rs), Pw rs (Sold s S) x * alpha (Aset s S) (Cmix s (Qs rs) S x) ≤
      GS s * (Pi1 rs - 1) := by
  have hv' := hv.2.2.2.2.2
  calc ∑ x ∈ range (Qs rs), Pw rs (Sold s S) x * alpha (Aset s S) (Cmix s (Qs rs) S x)
      ≤ ∑ x ∈ range (Qs rs), Pw rs (Sold s S) x *
          ∑ c ∈ Smix s S, (if x ≡ c.r [MOD c.d.gcd (Qs rs)] then gS s (kx s c) else 0) :=
        sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (alpha_le_sum hv hS x) (hP x))
    _ = ∑ c ∈ Smix s S, gS s (kx s c) *
          ∑ x ∈ (range (Qs rs)).filter (fun x => x ≡ c.r [MOD c.d.gcd (Qs rs)]),
            Pw rs (Sold s S) x := by
        simp_rw [mul_sum]
        rw [sum_comm]
        apply sum_congr rfl; intro c _
        rw [sum_filter]
        apply sum_congr rfl; intro x _
        split_ifs <;> ring
    _ ≤ ∑ c ∈ Smix s S, gS s (kx s c) * nu rs (c.d.gcd (Qs rs)) :=
        sum_le_sum (fun c _ => mul_le_mul_of_nonneg_left
          (hcls _ c.r (Nat.gcd_dvd_right _ _)) (gS_nonneg s _))
    _ = ∑ c ∈ Smix s S, (fun m j => gS s j * nu rs m) (c.d.gcd (Qs rs)) (kx s c) := rfl
    _ ≤ ∑ m ∈ (Qs rs).divisors.erase 1, ∑ j ∈ Icc 1 s.e, gS s j * nu rs m :=
        mix_sum_le hv hS _ (fun m j => mul_nonneg (gS_nonneg s j) (nu_nonneg rs hv' m))
    _ = GS s * (Pi1 rs - 1) := by
        rw [← sum_nu_erase hv', GS, mul_sum]
        apply sum_congr rfl; intro m _
        rw [sum_mul]

theorem both_le {m1 m2 r1 r2 : ℕ} (h1 : m1 ∣ Qs rs) (h2 : m2 ∣ Qs rs) :
    ∑ x ∈ range (Qs rs), (if x ≡ r1 [MOD m1] ∧ x ≡ r2 [MOD m2] then Pw rs (Sold s S) x else 0)
      ≤ nu rs (m1.lcm m2) := by
  by_cases hex : ∃ x0 ∈ range (Qs rs), x0 ≡ r1 [MOD m1] ∧ x0 ≡ r2 [MOD m2]
  · obtain ⟨x0, _, hx1, hx2⟩ := hex
    calc ∑ x ∈ range (Qs rs), (if x ≡ r1 [MOD m1] ∧ x ≡ r2 [MOD m2] then Pw rs (Sold s S) x else 0)
        ≤ ∑ x ∈ range (Qs rs), (if x ≡ x0 [MOD m1.lcm m2] then Pw rs (Sold s S) x else 0) := by
          apply sum_le_sum; intro x _
          split_ifs with ha hb
          · exact le_rfl
          · exact absurd (modEq_lcm (ha.1.trans hx1.symm) (ha.2.trans hx2.symm)) hb
          · exact hP x
          · exact le_rfl
      _ = ∑ x ∈ (range (Qs rs)).filter (fun x => x ≡ x0 [MOD m1.lcm m2]), Pw rs (Sold s S) x := by
          rw [sum_filter]
      _ ≤ nu rs (m1.lcm m2) := hcls _ x0 (Nat.lcm_dvd h1 h2)
  · push_neg at hex
    rw [sum_eq_zero (fun x hx => by rw [if_neg (fun h => hex x hx h.1 h.2)])]
    exact nu_nonneg rs hv.2.2.2.2.2 _

theorem second_moment :
    ∑ x ∈ range (Qs rs), Pw rs (Sold s S) x * alpha (Aset s S) (Cmix s (Qs rs) S x) ^ 2 ≤
      GS s ^ 2 * (Pi2 rs - 2 * Pi1 rs + 1) := by
  have hv' := hv.2.2.2.2.2
  set I : Cls → ℕ → ℚ := fun c x => if x ≡ c.r [MOD c.d.gcd (Qs rs)] then gS s (kx s c) else 0
  have hI0 : ∀ c x, 0 ≤ I c x := fun c x => by
    simp only [I]; split_ifs
    · exact gS_nonneg s _
    · exact le_rfl
  have hprod : ∀ c1 c2 : Cls, ∑ x ∈ range (Qs rs), Pw rs (Sold s S) x * (I c1 x * I c2 x) ≤
      gS s (kx s c1) * gS s (kx s c2) * nu rs ((c1.d.gcd (Qs rs)).lcm (c2.d.gcd (Qs rs))) := by
    intro c1 c2
    have hb := both_le hv hS hP hcls (r1 := c1.r) (r2 := c2.r) (Nat.gcd_dvd_right c1.d (Qs rs))
      (Nat.gcd_dvd_right c2.d (Qs rs))
    calc ∑ x ∈ range (Qs rs), Pw rs (Sold s S) x * (I c1 x * I c2 x)
        = gS s (kx s c1) * gS s (kx s c2) * ∑ x ∈ range (Qs rs),
            (if x ≡ c1.r [MOD c1.d.gcd (Qs rs)] ∧ x ≡ c2.r [MOD c2.d.gcd (Qs rs)] then
              Pw rs (Sold s S) x else 0) := by
          rw [mul_sum]; apply sum_congr rfl; intro x _
          simp only [I]
          by_cases ha : x ≡ c1.r [MOD c1.d.gcd (Qs rs)] <;>
            by_cases hb : x ≡ c2.r [MOD c2.d.gcd (Qs rs)] <;> simp [ha, hb] <;> ring
      _ ≤ gS s (kx s c1) * gS s (kx s c2) * nu rs ((c1.d.gcd (Qs rs)).lcm (c2.d.gcd (Qs rs))) :=
          mul_le_mul_of_nonneg_left hb (mul_nonneg (gS_nonneg s _) (gS_nonneg s _))
  calc ∑ x ∈ range (Qs rs), Pw rs (Sold s S) x * alpha (Aset s S) (Cmix s (Qs rs) S x) ^ 2
      ≤ ∑ x ∈ range (Qs rs), Pw rs (Sold s S) x * (∑ c ∈ Smix s S, I c x) ^ 2 := by
        apply sum_le_sum; intro x _
        apply mul_le_mul_of_nonneg_left _ (hP x)
        exact pow_le_pow_left₀ alpha_nonneg (alpha_le_sum hv hS x) 2
    _ = ∑ c1 ∈ Smix s S, ∑ c2 ∈ Smix s S,
          ∑ x ∈ range (Qs rs), Pw rs (Sold s S) x * (I c1 x * I c2 x) := by
        simp_rw [sq, sum_mul_sum, mul_sum]
        rw [sum_comm]
        apply sum_congr rfl; intro c1 _
        rw [sum_comm]
    _ ≤ ∑ c1 ∈ Smix s S, ∑ c2 ∈ Smix s S,
          gS s (kx s c1) * gS s (kx s c2) * nu rs ((c1.d.gcd (Qs rs)).lcm (c2.d.gcd (Qs rs))) :=
        sum_le_sum (fun c1 _ => sum_le_sum (fun c2 _ => hprod c1 c2))
    _ ≤ ∑ c1 ∈ Smix s S, ∑ m ∈ (Qs rs).divisors.erase 1, ∑ j ∈ Icc 1 s.e,
          gS s (kx s c1) * gS s j * nu rs ((c1.d.gcd (Qs rs)).lcm m) := by
        apply sum_le_sum; intro c1 _
        exact mix_sum_le hv hS (fun m j => gS s (kx s c1) * gS s j * nu rs ((c1.d.gcd (Qs rs)).lcm m))
          (fun m j => mul_nonneg (mul_nonneg (gS_nonneg s _) (gS_nonneg s _)) (nu_nonneg rs hv' _))
    _ ≤ ∑ m' ∈ (Qs rs).divisors.erase 1, ∑ j' ∈ Icc 1 s.e, ∑ m ∈ (Qs rs).divisors.erase 1,
          ∑ j ∈ Icc 1 s.e, gS s j' * gS s j * nu rs (m'.lcm m) := by
        exact mix_sum_le hv hS (fun m' j' => ∑ m ∈ (Qs rs).divisors.erase 1, ∑ j ∈ Icc 1 s.e,
          gS s j' * gS s j * nu rs (m'.lcm m))
          (fun m' j' => sum_nonneg (fun m _ => sum_nonneg (fun j _ =>
            mul_nonneg (mul_nonneg (gS_nonneg s _) (gS_nonneg s _)) (nu_nonneg rs hv' _))))
    _ = GS s ^ 2 * (Pi2 rs - 2 * Pi1 rs + 1) := by
        rw [← sum_nu2_erase hv', mul_sum]
        apply sum_congr rfl; intro m' _
        rw [sum_comm, mul_sum]
        apply sum_congr rfl; intro m _
        rw [sq, GS, sum_mul_sum, sum_mul]
        apply sum_congr rfl; intro j' _
        rw [sum_mul]

theorem mixed_mass :
    ∑ n ∈ range (Qs (s :: rs)), (if Cmix s (Qs rs) S (n % Qs rs) (n % s.p ^ s.e) then
      Pw (s :: rs) S n else 0) ≤ term s (Pi1 rs) (Pi2 rs) := by
  have hd0 := hv.2.2.1
  have hd1 := hv.2.2.2.1
  have hA := Aset_nonempty hv hS
  have e1 : ∑ n ∈ range (Qs (s :: rs)), (if Cmix s (Qs rs) S (n % Qs rs) (n % s.p ^ s.e) then
      Pw (s :: rs) S n else 0) =
      ∑ x ∈ range (Qs rs), Pw rs (Sold s S) x * hitMass (alpha (Aset s S) (Cmix s (Qs rs) S x)) s.δ := by
    refine (sum_cons hv (fun x y => if Cmix s (Qs rs) S x y then
      Pw rs (Sold s S) x * wfib (Aset s S) (Cmix s (Qs rs) S x) s.δ y else 0)).trans ?_
    apply sum_congr rfl; intro x _
    rw [← sum_wfib_hit hA (Aset_sub S) hd0, mul_sum, sum_filter]
  rw [e1]
  have hb : ∀ x, hitMass (alpha (Aset s S) (Cmix s (Qs rs) S x)) s.δ ≤
      alpha (Aset s S) (Cmix s (Qs rs) S x) ∧ (0 < s.δ → hitMass (alpha (Aset s S)
        (Cmix s (Qs rs) S x)) s.δ ≤ alpha (Aset s S) (Cmix s (Qs rs) S x) ^ 2 /
          (4 * s.δ * (1 - s.δ))) :=
    fun x => hitMass_le hd0 hd1 alpha_nonneg (alpha_le_one hA)
  have b1 : ∑ x ∈ range (Qs rs), Pw rs (Sold s S) x *
      hitMass (alpha (Aset s S) (Cmix s (Qs rs) S x)) s.δ ≤ GS s * (Pi1 rs - 1) :=
    (sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hb x).1 (hP x))).trans
      (first_moment hv hS hP hcls)
  unfold term
  split_ifs with hδ
  · exact b1
  · have hδp : 0 < s.δ := lt_of_le_of_ne hd0 (Ne.symm hδ)
    have hden : 0 < 4 * s.δ * (1 - s.δ) := by
      apply mul_pos (by linarith); linarith
    refine le_min b1 ?_
    calc ∑ x ∈ range (Qs rs), Pw rs (Sold s S) x *
          hitMass (alpha (Aset s S) (Cmix s (Qs rs) S x)) s.δ
        ≤ ∑ x ∈ range (Qs rs), Pw rs (Sold s S) x *
          (alpha (Aset s S) (Cmix s (Qs rs) S x) ^ 2 / (4 * s.δ * (1 - s.δ))) :=
          sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left ((hb x).2 hδp) (hP x))
      _ = (∑ x ∈ range (Qs rs), Pw rs (Sold s S) x *
          alpha (Aset s S) (Cmix s (Qs rs) S x) ^ 2) / (4 * s.δ * (1 - s.δ)) := by
          rw [sum_div]; apply sum_congr rfl; intro x _; ring
      _ ≤ GS s ^ 2 * (Pi2 rs - 2 * Pi1 rs + 1) / (4 * s.δ * (1 - s.δ)) :=
          div_le_div_of_nonneg_right (second_moment hv hS hP hcls) hden.le

theorem Pw_cons_cov (hcov : ∑ x ∈ (range (Qs rs)).filter (covd (Sold s S)), Pw rs (Sold s S) x ≤
      eta rs) :
    ∑ n ∈ (range (Qs (s :: rs))).filter (covd S), Pw (s :: rs) S n ≤ eta (s :: rs) := by
  have hA := Aset_nonempty hv hS
  have hPn := Pw_cons_nonneg (S := S) hv hP
  rw [sum_filter]
  calc ∑ n ∈ range (Qs (s :: rs)), (if covd S n then Pw (s :: rs) S n else 0)
      ≤ ∑ n ∈ range (Qs (s :: rs)), ((if covd (Sold s S) (n % Qs rs) then Pw (s :: rs) S n else 0) +
          (if n % s.p ^ s.e ∉ Aset s S then Pw (s :: rs) S n else 0) +
          (if Cmix s (Qs rs) S (n % Qs rs) (n % s.p ^ s.e) then Pw (s :: rs) S n else 0)) := by
        apply sum_le_sum; intro n _
        split_ifs with h0 h1 h2 h3 <;> first
          | (have := hPn n; linarith)
          | (exfalso; rcases covd_split hv hS h0 with h | h | h <;> contradiction)
          | (simp)
    _ = ∑ n ∈ range (Qs (s :: rs)), (if covd (Sold s S) (n % Qs rs) then Pw (s :: rs) S n else 0) +
        ∑ n ∈ range (Qs (s :: rs)), (if n % s.p ^ s.e ∉ Aset s S then Pw (s :: rs) S n else 0) +
        ∑ n ∈ range (Qs (s :: rs)), (if Cmix s (Qs rs) S (n % Qs rs) (n % s.p ^ s.e) then
          Pw (s :: rs) S n else 0) := by
        rw [sum_add_distrib, sum_add_distrib]
    _ ≤ eta rs + 0 + term s (Pi1 rs) (Pi2 rs) := by
        gcongr
        · -- old classes
          have e : ∑ n ∈ range (Qs (s :: rs)), (if covd (Sold s S) (n % Qs rs) then
              Pw (s :: rs) S n else 0) =
              ∑ x ∈ (range (Qs rs)).filter (covd (Sold s S)), Pw rs (Sold s S) x := by
            refine (sum_cons hv (fun x y => if covd (Sold s S) x then
              Pw rs (Sold s S) x * wfib (Aset s S) (Cmix s (Qs rs) S x) s.δ y else 0)).trans ?_
            rw [sum_filter]
            apply sum_congr rfl; intro x _
            split_ifs
            · rw [← mul_sum, sum_wfib hA hv.2.2.1 hv.2.2.2.1 (Aset_sub S), mul_one]
            · simp
          rw [e]; exact hcov
        · -- pure classes: zero weight off `A`
          apply le_of_eq
          apply sum_eq_zero; intro n _
          split_ifs with h <;> first
            | rfl
            | (rw [Pw_cons]; unfold wfib; rw [if_neg h, mul_zero])
        · exact mixed_mass hv hS hP hcls
    _ = eta (s :: rs) := by rw [add_zero]; rfl

end Moments

end Cover

/-! ### The induction -/

def Props (rs : List Stage) (S : Finset Cls) : Prop :=
  (∀ n, 0 ≤ Pw rs S n) ∧
  (∑ n ∈ range (Qs rs), Pw rs S n = 1) ∧
  (∀ m b, m ∣ Qs rs →
    ∑ n ∈ (range (Qs rs)).filter (fun n => n ≡ b [MOD m]), Pw rs S n ≤ nu rs m) ∧
  (∑ n ∈ (range (Qs rs)).filter (covd S), Pw rs S n ≤ eta rs)

theorem props : ∀ rs : List Stage, Valid rs → ∀ S, Fam (Qs rs) S → Props rs S
  | [], _, S, hS => by
    refine ⟨fun _ => zero_le_one, by simp [Qs, Pw], ?_, ?_⟩
    · intro m b _
      calc ∑ n ∈ (range (Qs [])).filter (fun n => n ≡ b [MOD m]), Pw [] S n
          ≤ ∑ n ∈ range (Qs []), Pw [] S n :=
            sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => zero_le_one)
        _ = nu [] m := by simp [Qs, Pw, nu]
    · have : (range (Qs [])).filter (covd S) = ∅ := by
        apply filter_eq_empty_iff.mpr
        rintro n - ⟨c, hc, _⟩
        have h1 := hS.gt c hc
        have h2 := Nat.le_of_dvd Nat.one_pos (hS.dvd c hc)
        simp [Qs] at h2; omega
      rw [this, sum_empty]; exact le_rfl
  | s :: rs, hv, S, hS => by
    obtain ⟨hP, hm, hc, hcv⟩ := props rs hv.2.2.2.2.2 (Sold s S) (fam_old hv hS)
    exact ⟨Pw_cons_nonneg hv hP, Pw_cons_mass hv hS hm, Pw_cons_class hv hS hP hc,
      Pw_cons_cov hv hS hP hc hcv⟩

/-- **Soundness of the distorted tower certificate.** If a family with distinct moduli `> 1`
dividing `Qs rs` covers every residue, then `eta rs ≥ 1`. -/
theorem one_le_eta {rs : List Stage} (hv : Valid rs) {S : Finset Cls} (hS : Fam (Qs rs) S)
    (hcov : ∀ n, n < Qs rs → covd S n) : 1 ≤ eta rs := by
  obtain ⟨_, hm, _, hcv⟩ := props rs hv S hS
  have : (range (Qs rs)).filter (covd S) = range (Qs rs) :=
    filter_true_of_mem (fun n hn => hcov n (mem_range.mp hn))
  rw [this, hm] at hcv
  exact hcv

end Covering.Hybrid
