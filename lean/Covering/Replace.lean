/-
Prime replacement (Simpson–Zeilberger, Acta Arith. 59 (1991), Thm 1; see also Schroeder 2026,
Lemma 2.1), for arbitrary exponents.

If `p ≤ q` are primes, `M` is coprime to both, and there is a covering with distinct moduli
`> 1` dividing `M · q^e`, then there is one with moduli dividing `M · p^e`.

Proof: the digit map `ι : ℤ/p^e → ℤ/q^e` keeps base-`p` digits as base-`q` digits. A class
modulo `q^v` (fixing the first `v` base-`q` digits) pulls back to the empty set or to a class
modulo `p^v` (`iota_modEq`). Combining with the identity on the `M`-coordinate by CRT, each
class `c (mod d₁ q^v)` pulls back into a class modulo `d₁ p^v`; distinct moduli stay distinct.
-/
import Covering.Phi

namespace Covering

open Finset

/-! ### Digit maps -/

/-- `iota p q A n`: write the last `A` base-`p` digits of `n` in base `q`. -/
def iota (p q : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | A + 1, n => n % p + q * iota p q A (n / p)

/-- `dig p q v r`: write the last `v` base-`q` digits of `r` in base `p`. -/
def dig (p q : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | v + 1, r => r % q + p * dig p q v (r / q)

theorem modEq_split {a b m k : ℕ} (h : a ≡ b [MOD m * k]) :
    a % m = b % m ∧ a / m ≡ b / m [MOD k] := by
  unfold Nat.ModEq at h ⊢
  constructor
  · rw [← Nat.mod_mul_right_mod a m k, h, Nat.mod_mul_right_mod]
  · rw [← Nat.mod_mul_right_div_self a m k, h, Nat.mod_mul_right_div_self]

theorem modEq_join {a b m k : ℕ} (h1 : a % m = b % m) (h2 : a / m ≡ b / m [MOD k]) :
    a ≡ b [MOD m * k] := by
  unfold Nat.ModEq at h2 ⊢
  rw [Nat.mod_mul, Nat.mod_mul (a := m) (b := k) (x := b), h1, h2]

/-- A class modulo `q^v` pulls back under the digit map into a class modulo `p^v`. -/
theorem iota_modEq {p q : ℕ} (hp : 0 < p) (hpq : p ≤ q) :
    ∀ v A n r, v ≤ A → iota p q A n ≡ r [MOD q ^ v] → n ≡ dig p q v r [MOD p ^ v] := by
  intro v
  induction v with
  | zero => intro A n r _ _; simp [Nat.ModEq, pow_zero, Nat.mod_one]
  | succ v ih =>
    intro A n r hvA h
    cases A with
    | zero => omega
    | succ A =>
      have hq : 0 < q := lt_of_lt_of_le hp hpq
      rw [pow_succ'] at h
      obtain ⟨h1, h2⟩ := modEq_split h
      simp only [iota] at h1 h2
      have hlt : n % p < q := lt_of_lt_of_le (Nat.mod_lt n hp) hpq
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt] at h1
      rw [Nat.add_mul_div_left _ _ hq, Nat.div_eq_of_lt hlt, zero_add] at h2
      have ih' := ih A (n / p) (r / q) (by omega) h2
      have hr : r % q < p := h1 ▸ Nat.mod_lt n hp
      rw [pow_succ']
      simp only [dig]
      apply modEq_join
      · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr, h1]
      · rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hr, zero_add]
        exact ih'

/-! ### Single-prime replacement -/

theorem eq_of_mul_pow_eq {a b p i j : ℕ} (hp : p.Prime) (ha : a.Coprime p) (hb : b.Coprime p)
    (h : a * p ^ i = b * p ^ j) : a = b ∧ i = j := by
  have ha0 : a ≠ 0 := by
    rintro rfl; exact hp.one_lt.ne' (Nat.coprime_zero_left _ |>.mp ha)
  have hb0 : b ≠ 0 := by
    rintro rfl; exact hp.one_lt.ne' (Nat.coprime_zero_left _ |>.mp hb)
  have hna : ¬ p ∣ a := (Nat.Prime.coprime_iff_not_dvd hp).mp ha.symm
  have hnb : ¬ p ∣ b := (Nat.Prime.coprime_iff_not_dvd hp).mp hb.symm
  have hf : ∀ c k, c ≠ 0 → ¬ p ∣ c → (c * p ^ k).factorization p = k := by
    intro c k hc hnc
    rw [Nat.factorization_mul hc (pow_ne_zero _ hp.ne_zero), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hnc, hp.factorization_pow, Finsupp.single_eq_same,
      zero_add]
  have hij : i = j := by rw [← hf a i ha0 hna, h, hf b j hb0 hnb]
  subst hij
  exact ⟨mul_right_cancel₀ (pow_ne_zero _ hp.ne_zero) h, rfl⟩

section Replace

variable {M p q e : ℕ}

/-- The decomposition `d = gcd(d, M) · q^v` of a divisor of `M q^e`. -/
theorem split_dvd (hq : q.Prime) (hMq : M.Coprime q) {d : ℕ} (hd : d ∣ M * q ^ e) :
    ∃ v ≤ e, d = d.gcd M * q ^ v := by
  have h1 : d.gcd (M * q ^ e) = d.gcd M * d.gcd (q ^ e) := Nat.Coprime.gcd_mul d (hMq.pow_right e)
  rw [Nat.gcd_eq_left hd] at h1
  obtain ⟨v, hv, hv'⟩ := (Nat.dvd_prime_pow hq).mp (Nat.gcd_dvd_right d (q ^ e))
  exact ⟨v, hv, by rw [← hv']; exact h1⟩

/-- Exponent of `q` in `c.d`, and the cofactor. -/
noncomputable def vq (q e M : ℕ) (c : Cls) : ℕ :=
  by classical exact if h : ∃ v ≤ e, c.d = c.d.gcd M * q ^ v then Classical.choose h else 0

theorem vq_spec (hq : q.Prime) (hMq : M.Coprime q) {c : Cls} (hd : c.d ∣ M * q ^ e) :
    vq q e M c ≤ e ∧ c.d = c.d.gcd M * q ^ vq q e M c := by
  classical
  have h := split_dvd (e := e) hq hMq hd
  unfold vq
  rw [dif_pos h]
  exact Classical.choose_spec h

theorem cop_d1 (hMp : M.Coprime p) (c : Cls) (v : ℕ) : (c.d.gcd M).Coprime (p ^ v) :=
  Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right _ _) (hMp.pow_right v)

/-- The pulled-back class. -/
noncomputable def pull (p q e M : ℕ) (hMp : M.Coprime p) (c : Cls) : Cls :=
  ⟨(Nat.chineseRemainder (cop_d1 hMp c (vq q e M c)) c.r (dig p q (vq q e M c) c.r)).1,
    c.d.gcd M * p ^ vq q e M c⟩

theorem replace_one (hq : q.Prime) (hp : p.Prime) (hpq : p ≤ q) (hMq : M.Coprime q)
    (hMp : M.Coprime p) {S : Finset Cls} (hS : IsCovering (M * q ^ e) S) :
    IsCovering (M * p ^ e) (S.image (pull p q e M hMp)) := by
  classical
  have hM : 0 < M := Nat.pos_of_ne_zero (by
    rintro rfl; have := hS.pos; simp at this)
  refine ⟨Nat.mul_pos hM (pow_pos hp.pos _), ?_, ?_, ?_, ?_⟩
  · -- moduli divide
    intro c' hc'
    obtain ⟨c, hc, rfl⟩ := mem_image.mp hc'
    obtain ⟨hv, _⟩ := vq_spec (e := e) hq hMq (hS.dvd c hc)
    exact mul_dvd_mul (Nat.gcd_dvd_right _ _) (pow_dvd_pow p hv)
  · -- moduli > 1
    intro c' hc'
    obtain ⟨c, hc, rfl⟩ := mem_image.mp hc'
    obtain ⟨_, hsplit⟩ := vq_spec (e := e) hq hMq (hS.dvd c hc)
    have hgt := hS.gt c hc
    show 1 < c.d.gcd M * p ^ vq q e M c
    have hg0 : 0 < c.d.gcd M := Nat.gcd_pos_of_pos_right _ hM
    rcases Nat.eq_zero_or_pos (vq q e M c) with h0 | hpos
    · rw [h0, pow_zero, mul_one] at hsplit ⊢
      omega
    · have : 1 < p ^ vq q e M c := Nat.one_lt_pow hpos.ne' hp.one_lt
      calc 1 < p ^ vq q e M c := this
        _ ≤ c.d.gcd M * p ^ vq q e M c := Nat.le_mul_of_pos_left _ hg0
  · -- distinct moduli
    intro c1' hc1' c2' hc2' hd
    obtain ⟨c1, hc1, rfl⟩ := mem_image.mp hc1'
    obtain ⟨c2, hc2, rfl⟩ := mem_image.mp hc2'
    have e1 := (vq_spec (e := e) hq hMq (hS.dvd c1 hc1)).2
    have e2 := (vq_spec (e := e) hq hMq (hS.dvd c2 hc2)).2
    obtain ⟨hg, hv⟩ := eq_of_mul_pow_eq hp
      (Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right _ _) hMp)
      (Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right _ _) hMp) hd
    have : c1.d = c2.d := by rw [e1, e2, hg, hv]
    rw [hS.inj c1 hc1 c2 hc2 this]
  · -- covering
    intro n hn
    have hco : M.Coprime (q ^ e) := hMq.pow_right e
    set w := iota p q e (n % p ^ e)
    obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hco n w
    set z := k % (M * q ^ e)
    have hz : z < M * q ^ e := Nat.mod_lt _ (Nat.mul_pos hM (pow_pos hq.pos _))
    have hzk : z ≡ k [MOD M * q ^ e] := Nat.mod_modEq _ _
    have hzn : z ≡ n [MOD M] := (hzk.of_dvd (dvd_mul_right _ _)).trans hk1
    have hzw : z ≡ w [MOD q ^ e] := (hzk.of_dvd (dvd_mul_left _ _)).trans hk2
    obtain ⟨c, hc, hzc⟩ := hS.cov z hz
    obtain ⟨hv, hsplit⟩ := vq_spec (e := e) hq hMq (hS.dvd c hc)
    set v := vq q e M c
    refine ⟨pull p q e M hMp c, mem_image_of_mem _ hc, ?_⟩
    have hd1 : c.d.gcd M ∣ c.d := Nat.gcd_dvd_left _ _
    have hqv : q ^ v ∣ c.d := by rw [hsplit]; exact dvd_mul_left _ _
    -- the M-part
    have hA : n ≡ c.r [MOD c.d.gcd M] :=
      (hzn.of_dvd (Nat.gcd_dvd_right _ _)).symm.trans (hzc.of_dvd hd1)
    -- the q-part, pulled back
    have hB : w ≡ c.r [MOD q ^ v] :=
      (hzw.of_dvd (pow_dvd_pow q hv)).symm.trans (hzc.of_dvd hqv)
    have hB' := iota_modEq hp.pos hpq v e (n % p ^ e) c.r hv hB
    have hB'' : n ≡ dig p q v c.r [MOD p ^ v] :=
      (((Nat.mod_modEq n (p ^ e)).of_dvd (pow_dvd_pow p hv)).symm).trans hB'
    obtain ⟨r', hr1, hr2⟩ := Nat.chineseRemainder (cop_d1 hMp c v) c.r (dig p q v c.r)
    show n ≡ (Nat.chineseRemainder (cop_d1 hMp c v) c.r (dig p q v c.r)).1
      [MOD c.d.gcd M * p ^ v]
    have hC := (Nat.chineseRemainder (cop_d1 hMp c v) c.r (dig p q v c.r)).2
    exact (Nat.modEq_and_modEq_iff_modEq_mul (cop_d1 hMp c v)).mp
      ⟨hA.trans hC.1.symm, hB''.trans hC.2.symm⟩

end Replace

end Covering
