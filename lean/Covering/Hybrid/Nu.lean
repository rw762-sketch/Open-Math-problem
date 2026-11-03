/-
Stages of the distorted tower sieve: tower numbers, the class weight `nu`, the products `Pi1`,
`Pi2`, and the certificate value `eta`. Divisor-sum identities for `nu`.

Stages are listed in *reverse* exposure order: `s :: rs` means `s` is exposed after `rs`,
and `Qs (s :: rs) = Qs rs * s.p ^ s.e`.
-/
import Covering.Hybrid.Fibre
import Covering.Replace

namespace Covering.Hybrid

open Finset

structure Stage where
  p : ℕ
  e : ℕ
  δ : ℚ

def Qs : List Stage → ℕ
  | [] => 1
  | s :: rs => Qs rs * s.p ^ s.e

/-- `u = p^e − (1 + p + ⋯ + p^{e−1})`. -/
def uS (s : Stage) : ℕ := s.p ^ s.e - ∑ j ∈ range s.e, s.p ^ j

def gS (s : Stage) (v : ℕ) : ℚ := ((min (s.p ^ (s.e - v)) (uS s) : ℕ) : ℚ) / (uS s : ℚ)

def cS (s : Stage) : ℚ := 1 / (1 - s.δ)

def γS (s : Stage) (v : ℕ) : ℚ := if v = 0 then 1 else cS s * gS s v

def GS (s : Stage) : ℚ := ∑ v ∈ Icc 1 s.e, gS s v

def Pi1 : List Stage → ℚ
  | [] => 1
  | s :: rs => Pi1 rs * ∑ v ∈ range (s.e + 1), γS s v

def Pi2 : List Stage → ℚ
  | [] => 1
  | s :: rs => Pi2 rs * ∑ a ∈ range (s.e + 1), ∑ b ∈ range (s.e + 1), γS s (max a b)

def term (s : Stage) (P1 P2 : ℚ) : ℚ :=
  if s.δ = 0 then GS s * (P1 - 1)
  else min (GS s * (P1 - 1)) (GS s ^ 2 * (P2 - 2 * P1 + 1) / (4 * s.δ * (1 - s.δ)))

def eta : List Stage → ℚ
  | [] => 0
  | s :: rs => eta rs + term s (Pi1 rs) (Pi2 rs)

def nu : List Stage → ℕ → ℚ
  | [], _ => 1
  | s :: rs, m => nu rs m * γS s (m.factorization s.p)

def Valid : List Stage → Prop
  | [] => True
  | s :: rs => s.p.Prime ∧ 1 ≤ s.e ∧ 0 ≤ s.δ ∧ s.δ ≤ 1 / 2 ∧ (Qs rs).Coprime s.p ∧ Valid rs

/-! ### Basic facts -/

theorem Qs_pos : ∀ rs : List Stage, Valid rs → 0 < Qs rs
  | [], _ => Nat.one_pos
  | s :: rs, ⟨hp, _, _, _, _, hv⟩ => Nat.mul_pos (Qs_pos rs hv) (pow_pos hp.pos _)

theorem stage_dvd : ∀ rs : List Stage, Valid rs → ∀ t ∈ rs, t.p ∣ Qs rs
  | [], _, t, ht => absurd ht (List.not_mem_nil)
  | s :: rs, ⟨hp, he, _, _, _, hv⟩, t, ht => by
    rcases List.mem_cons.mp ht with rfl | ht'
    · exact dvd_mul_of_dvd_right (dvd_pow_self _ (by omega)) _
    · exact dvd_mul_of_dvd_left (stage_dvd rs hv t ht') _

theorem stage_prime : ∀ rs : List Stage, Valid rs → ∀ t ∈ rs, t.p.Prime
  | [], _, t, ht => absurd ht (List.not_mem_nil)
  | s :: rs, ⟨hp, _, _, _, _, hv⟩, t, ht => by
    rcases List.mem_cons.mp ht with rfl | ht'
    · exact hp
    · exact stage_prime rs hv t ht'

theorem stage_ne {s : Stage} {rs : List Stage} (hv : Valid (s :: rs)) : ∀ t ∈ rs, t.p ≠ s.p := by
  obtain ⟨hp, _, _, _, hcop, hv'⟩ := hv
  intro t ht heq
  have := stage_dvd rs hv' t ht
  rw [heq] at this
  exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop.symm this)

/-- `nu rs m` only depends on the exponents of the stage primes in `m`. -/
theorem nu_congr : ∀ (rs : List Stage) (m m' : ℕ), (∀ t ∈ rs, m.factorization t.p = m'.factorization t.p) →
    nu rs m = nu rs m'
  | [], _, _, _ => rfl
  | s :: rs, m, m', h => by
    simp only [nu]
    rw [nu_congr rs m m' (fun t ht => h t (List.mem_cons_of_mem _ ht)), h s (List.mem_cons_self ..)]

theorem nu_one : ∀ rs : List Stage, nu rs 1 = 1
  | [] => rfl
  | s :: rs => by simp [nu, nu_one rs, γS]

theorem uS_pos {s : Stage} (hp : s.p.Prime) : 0 < uS s := by
  have := geomSum_lt_pw (L := s.p ^ s.e) hp
  unfold uS
  have hex : (s.p ^ s.e).factorization s.p = s.e := by rw [hp.factorization_pow]; simp
  simp only [ex, pw, hex] at this
  omega

theorem gS_nonneg (s : Stage) (v : ℕ) : 0 ≤ gS s v := by unfold gS; positivity

theorem cS_pos {s : Stage} (h1 : s.δ ≤ 1 / 2) : 0 < cS s := by
  unfold cS; apply div_pos one_pos; linarith

theorem γS_nonneg {s : Stage} (h1 : s.δ ≤ 1 / 2) (v : ℕ) : 0 ≤ γS s v := by
  unfold γS; split_ifs
  · exact zero_le_one
  · exact mul_nonneg (cS_pos h1).le (gS_nonneg s v)

theorem nu_nonneg : ∀ rs : List Stage, Valid rs → ∀ m, 0 ≤ nu rs m
  | [], _, _ => zero_le_one
  | s :: rs, ⟨_, _, _, h1, _, hv⟩, m => mul_nonneg (nu_nonneg rs hv m) (γS_nonneg h1 _)

/-! ### Divisors of `Q p^e` -/

theorem fac_mul_pow {a p v : ℕ} (hp : p.Prime) (ha : a ≠ 0) (hna : ¬ p ∣ a) :
    (a * p ^ v).factorization p = v := by
  rw [Nat.factorization_mul ha (pow_ne_zero _ hp.ne_zero), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hna, hp.factorization_pow, Finsupp.single_eq_same,
    zero_add]

theorem fac_mul_pow_other {a p v q : ℕ} (hp : p.Prime) (ha : a ≠ 0) (hq : q ≠ p) :
    (a * p ^ v).factorization q = a.factorization q := by
  rw [Nat.factorization_mul ha (pow_ne_zero _ hp.ne_zero), Finsupp.add_apply, hp.factorization_pow,
    Finsupp.single_eq_of_ne (Ne.symm hq), add_zero]

theorem sum_divisors_mul_pow {Q p e : ℕ} (hp : p.Prime) (hQ : 0 < Q) (hcop : Q.Coprime p)
    (F : ℕ → ℚ) :
    ∑ m ∈ (Q * p ^ e).divisors, F m = ∑ a ∈ Q.divisors, ∑ v ∈ range (e + 1), F (a * p ^ v) := by
  rw [← Finset.sum_product' (f := fun a v => F (a * p ^ v))]
  symm
  have hQe : Q * p ^ e ≠ 0 := mul_ne_zero hQ.ne' (pow_ne_zero _ hp.ne_zero)
  have hnQ : ¬ p ∣ Q := (Nat.Prime.coprime_iff_not_dvd hp).mp hcop.symm
  apply Finset.sum_nbij' (fun x => x.1 * p ^ x.2) (fun m => (m.gcd Q, m.factorization p))
  · intro x hx
    simp only [mem_product, Nat.mem_divisors, mem_range] at hx ⊢
    exact ⟨mul_dvd_mul hx.1.1 (pow_dvd_pow p (by omega)), hQe⟩
  · intro m hm
    simp only [mem_product, Nat.mem_divisors, mem_range] at hm ⊢
    refine ⟨⟨Nat.gcd_dvd_right _ _, hQ.ne'⟩, ?_⟩
    have h1 := (Nat.factorization_le_iff_dvd (Nat.pos_of_dvd_of_pos hm.1 (Nat.pos_of_ne_zero hQe)).ne'
      hQe).mpr hm.1
    have h2 := h1 p
    rw [fac_mul_pow hp hQ.ne' hnQ] at h2
    omega
  · intro x hx
    simp only [mem_product, Nat.mem_divisors, mem_range] at hx
    have hx0 : x.1 ≠ 0 := fun h => by rw [h] at hx; exact hQ.ne' (Nat.eq_zero_of_zero_dvd hx.1.1)
    have hnx : ¬ p ∣ x.1 := fun h => hnQ (dvd_trans h hx.1.1)
    ext
    · show (x.1 * p ^ x.2).gcd Q = x.1
      rw [Nat.Coprime.gcd_mul_right_cancel _ (hcop.symm.pow_left _), Nat.gcd_eq_left hx.1.1]
    · exact fac_mul_pow hp hx0 hnx
  · intro m hm
    simp only [Nat.mem_divisors] at hm
    obtain ⟨v, _, hv⟩ := split_dvd (e := e) hp hcop hm.1
    show m.gcd Q * p ^ m.factorization p = m
    have hg0 : m.gcd Q ≠ 0 := (Nat.gcd_pos_of_pos_right _ hQ).ne'
    have hng : ¬ p ∣ m.gcd Q := fun h => hnQ (dvd_trans h (Nat.gcd_dvd_right _ _))
    have : m.factorization p = v := by
      conv_lhs => rw [hv]
      exact fac_mul_pow hp hg0 hng
    rw [this, ← hv]
  · intro x _; rfl

/-! ### `Σ nu = Pi1`, `Σ nu(lcm) = Pi2` -/

theorem nu_cons_mul_pow {s : Stage} {rs : List Stage} (hv : Valid (s :: rs)) {a : ℕ} (ha : a ∣ Qs rs)
    (v : ℕ) : nu (s :: rs) (a * s.p ^ v) = nu rs a * γS s v := by
  obtain ⟨hp, _, _, _, hcop, hv'⟩ := hv
  have hQ := Qs_pos rs hv'
  have ha0 : a ≠ 0 := fun h => by rw [h] at ha; exact hQ.ne' (Nat.eq_zero_of_zero_dvd ha)
  have hna : ¬ s.p ∣ a := fun h =>
    hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop.symm (dvd_trans h ha))
  simp only [nu]
  rw [fac_mul_pow hp ha0 hna]
  congr 1
  apply nu_congr
  intro t ht
  exact fac_mul_pow_other hp ha0 (stage_ne ⟨hp, ‹_›, ‹_›, ‹_›, hcop, hv'⟩ t ht)

theorem sum_nu : ∀ rs : List Stage, Valid rs → ∑ m ∈ (Qs rs).divisors, nu rs m = Pi1 rs
  | [], _ => by simp [Qs, nu, Pi1]
  | s :: rs, hv => by
    obtain ⟨hp, he, hd0, hd1, hcop, hv'⟩ := hv
    have hvv : Valid (s :: rs) := ⟨hp, he, hd0, hd1, hcop, hv'⟩
    simp only [Qs]
    rw [sum_divisors_mul_pow hp (Qs_pos rs hv') hcop]
    rw [sum_congr rfl (fun a ha => sum_congr rfl (fun v _ =>
      nu_cons_mul_pow hvv (Nat.dvd_of_mem_divisors ha) v))]
    simp only [← mul_sum, ← sum_mul]
    rw [sum_nu rs hv', Pi1]

theorem modEq_lcm {a b m n : ℕ} (h1 : a ≡ b [MOD m]) (h2 : a ≡ b [MOD n]) :
    a ≡ b [MOD m.lcm n] := by
  apply Nat.modEq_of_dvd
  have d1 := (Int.natCast_dvd).mp h1.dvd
  have d2 := (Int.natCast_dvd).mp h2.dvd
  exact (Int.natCast_dvd).mpr (Nat.lcm_dvd d1 d2)

theorem nu_cons_lcm {s : Stage} {rs : List Stage} (hv : Valid (s :: rs)) {a b : ℕ} (ha : a ∣ Qs rs)
    (hb : b ∣ Qs rs) (v w : ℕ) :
    nu (s :: rs) ((a * s.p ^ v).lcm (b * s.p ^ w)) = nu rs (a.lcm b) * γS s (max v w) := by
  obtain ⟨hp, he, hd0, hd1, hcop, hv'⟩ := hv
  have hvv : Valid (s :: rs) := ⟨hp, he, hd0, hd1, hcop, hv'⟩
  have hQ := Qs_pos rs hv'
  have ha0 : a ≠ 0 := fun h => by rw [h] at ha; exact hQ.ne' (Nat.eq_zero_of_zero_dvd ha)
  have hb0 : b ≠ 0 := fun h => by rw [h] at hb; exact hQ.ne' (Nat.eq_zero_of_zero_dvd hb)
  have hna : ¬ s.p ∣ a := fun h =>
    hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop.symm (dvd_trans h ha))
  have hnb : ¬ s.p ∣ b := fun h =>
    hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop.symm (dvd_trans h hb))
  have hx0 : a * s.p ^ v ≠ 0 := mul_ne_zero ha0 (pow_ne_zero _ hp.ne_zero)
  have hy0 : b * s.p ^ w ≠ 0 := mul_ne_zero hb0 (pow_ne_zero _ hp.ne_zero)
  simp only [nu]
  rw [Nat.factorization_lcm hx0 hy0, Finsupp.sup_apply, fac_mul_pow hp ha0 hna,
    fac_mul_pow hp hb0 hnb]
  congr 1
  apply nu_congr
  intro t ht
  have hne := stage_ne hvv t ht
  rw [Nat.factorization_lcm hx0 hy0, Nat.factorization_lcm ha0 hb0, Finsupp.sup_apply,
    Finsupp.sup_apply, fac_mul_pow_other hp ha0 hne, fac_mul_pow_other hp hb0 hne]

theorem sum_nu2 : ∀ rs : List Stage, Valid rs →
    ∑ m ∈ (Qs rs).divisors, ∑ m' ∈ (Qs rs).divisors, nu rs (m.lcm m') = Pi2 rs
  | [], _ => by simp [Qs, nu, Pi2]
  | s :: rs, hv => by
    obtain ⟨hp, he, hd0, hd1, hcop, hv'⟩ := hv
    have hvv : Valid (s :: rs) := ⟨hp, he, hd0, hd1, hcop, hv'⟩
    simp only [Qs]
    rw [sum_divisors_mul_pow hp (Qs_pos rs hv') hcop]
    simp_rw [sum_divisors_mul_pow hp (Qs_pos rs hv') hcop]
    have : ∀ a ∈ (Qs rs).divisors, ∀ v ∈ range (s.e + 1), ∀ b ∈ (Qs rs).divisors,
        ∀ w ∈ range (s.e + 1),
        nu (s :: rs) ((a * s.p ^ v).lcm (b * s.p ^ w)) = nu rs (a.lcm b) * γS s (max v w) :=
      fun a ha v _ b hb w _ =>
        nu_cons_lcm hvv (Nat.dvd_of_mem_divisors ha) (Nat.dvd_of_mem_divisors hb) v w
    rw [sum_congr rfl (fun a ha => sum_congr rfl (fun v hv1 => sum_congr rfl (fun b hb =>
      sum_congr rfl (fun w hw => this a ha v hv1 b hb w hw))))]
    rw [Pi2, ← sum_nu2 rs hv', sum_mul]
    apply sum_congr rfl; intro a _
    rw [sum_comm, sum_mul]
    apply sum_congr rfl; intro b _
    rw [mul_sum]
    apply sum_congr rfl; intro v _
    rw [mul_sum]

end Covering.Hybrid
