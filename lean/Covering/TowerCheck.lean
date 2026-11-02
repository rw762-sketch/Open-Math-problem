/-
Decidable tower certificate and the headline theorem.
-/
import Covering.Tower
import Covering.Check

namespace Covering

open Finset

/-! ### p-adic valuation, kernel-evaluable -/

/-- `vpAux p n f` = number of times `p` divides `n` (fuel `f ≥ n` suffices). -/
def vpAux (p : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | f + 1, n => if 2 ≤ p ∧ 0 < n ∧ n % p = 0 then vpAux p f (n / p) + 1 else 0

def vp (p n : ℕ) : ℕ := vpAux p n n

theorem vpAux_spec (p : ℕ) (hp : 2 ≤ p) :
    ∀ f n, 0 < n → n ≤ f → p ^ vpAux p f n ∣ n ∧ ¬ p ^ (vpAux p f n + 1) ∣ n := by
  intro f
  induction f with
  | zero => intro n hn hf; omega
  | succ f ih =>
    intro n hn hf
    unfold vpAux
    by_cases h : 2 ≤ p ∧ 0 < n ∧ n % p = 0
    · rw [if_pos h]
      have hpd : p ∣ n := Nat.dvd_of_mod_eq_zero h.2.2
      have hq : 0 < n / p := Nat.div_pos (Nat.le_of_dvd hn hpd) (by omega)
      have hqf : n / p ≤ f := by
        have : n / p < n := Nat.div_lt_self hn (by omega)
        omega
      obtain ⟨h1, h2⟩ := ih (n / p) hq hqf
      have hn' : p * (n / p) = n := Nat.mul_div_cancel' hpd
      constructor
      · rw [pow_succ']
        have := Nat.mul_dvd_mul_left p h1
        rwa [hn'] at this
      · intro h3
        apply h2
        have h3' : p * p ^ (vpAux p f (n / p) + 1) ∣ p * (n / p) := by
          rw [hn', ← pow_succ']; exact h3
        exact Nat.dvd_of_mul_dvd_mul_left (k := p) (by omega) h3'
    · rw [if_neg h]
      refine ⟨one_dvd n, fun h1 => h ⟨hp, hn, ?_⟩⟩
      rw [pow_one] at h1
      exact Nat.mod_eq_zero_of_dvd h1

theorem vp_eq_factorization {p n : ℕ} (hp : p.Prime) (hn : 0 < n) : vp p n = n.factorization p := by
  obtain ⟨h1, h2⟩ := vpAux_spec p hp.two_le n n hn le_rfl
  have a := (hp.pow_dvd_iff_le_factorization hn.ne').mp h1
  have b : ¬ (vpAux p n n + 1 ≤ n.factorization p) :=
    fun h => h2 ((hp.pow_dvd_iff_le_factorization hn.ne').mpr h)
  unfold vp; omega

/-! ### The certificate in Finset form -/

/-- Summand of the tower certificate for divisor `d` of `L`. -/
def towerTerm (L d : ℕ) : ℚ :=
  ∏ p ∈ L.primeFactors, ((min (p ^ (ex L p - ex d p)) (uu L p) : ℕ) : ℚ) / (uu L p : ℚ)

def towerSum (L : ℕ) : ℚ :=
  ∑ d ∈ (Nat.divisors L).filter (fun d => 1 < d ∧ ¬ IsPrimePow d), towerTerm L d

theorem towerTerm_nonneg (L d : ℕ) : 0 ≤ towerTerm L d :=
  prod_nonneg (fun p _ => by positivity)

theorem no_covering_of_towerSum {L : ℕ} (h : towerSum L < 1) (S : Finset Cls) :
    ¬ IsCovering L S := by
  intro hS
  have hL := hS.pos
  have h1 := one_le_towerSum hS
  have hinj : Set.InjOn (fun c : Cls => c.d) (S.filter (fun c => ¬ IsPrimePow c.d)) :=
    fun c hc c' hc' h => hS.inj c (mem_filter.mp hc).1 c' (mem_filter.mp hc').1 h
  have h1' : ∑ d ∈ (S.filter (fun c => ¬ IsPrimePow c.d)).image (fun c : Cls => c.d), towerTerm L d
      = ∑ c ∈ S.filter (fun c => ¬ IsPrimePow c.d), towerTerm L c.d := sum_image hinj
  change 1 ≤ ∑ c ∈ S.filter (fun c => ¬ IsPrimePow c.d), towerTerm L c.d at h1
  rw [← h1'] at h1
  have hsub : (S.filter (fun c => ¬ IsPrimePow c.d)).image (fun c : Cls => c.d) ⊆
      (Nat.divisors L).filter (fun d => 1 < d ∧ ¬ IsPrimePow d) := by
    intro d hd
    rw [mem_image] at hd
    obtain ⟨c, hc, rfl⟩ := hd
    rw [mem_filter] at hc ⊢
    exact ⟨Nat.mem_divisors.mpr ⟨hS.dvd c hc.1, hL.ne'⟩, hS.gt c hc.1, hc.2⟩
  have h2 := sum_le_sum_of_subset_of_nonneg (f := towerTerm L) hsub (fun d _ _ => towerTerm_nonneg L d)
  unfold towerSum at h
  linarith

/-! ### Fast (list) form -/

/-- `u_p` computed from `p` and `e`. -/
def uuF (p e : ℕ) : ℕ := p ^ e - (p ^ e - 1) / (p - 1)

theorem uuF_eq {L p : ℕ} (hp : p.Prime) : uuF p (vp p L) = uu L p ∨ L = 0 := by
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · right; rfl
  · left
    unfold uuF uu pw
    rw [vp_eq_factorization hp hL, Nat.geomSum_eq hp.two_le]

/-- Number of primes of `L` dividing `d`. -/
def primeCount (L d : ℕ) : ℕ := ((primeList L).filter (fun p => decide (p ∣ d))).length

theorem primeFactors_of_dvd {L d : ℕ} (hL : 0 < L) (hd : d ∣ L) (hd0 : 0 < d) :
    d.primeFactors = ((primeList L).filter (fun p => decide (p ∣ d))).toFinset := by
  ext p
  rw [Nat.mem_primeFactors, List.mem_toFinset, List.mem_filter, primeList, List.mem_filter,
    mem_divList hL, isPrimeTD_iff, decide_eq_true_iff]
  constructor
  · rintro ⟨hp, hpd, _⟩; exact ⟨⟨hpd.trans hd, hp⟩, hpd⟩
  · rintro ⟨⟨_, hp⟩, hpd⟩; exact ⟨hp, hpd, hd0.ne'⟩

theorem isPrimePow_iff_primeCount {L d : ℕ} (hL : 0 < L) (hd : d ∣ L) (hd0 : 0 < d) :
    IsPrimePow d ↔ primeCount L d = 1 := by
  rw [isPrimePow_iff_card_primeFactors_eq_one, primeFactors_of_dvd hL hd hd0, primeCount,
    List.toFinset_card_of_nodup ((primeList_nodup hL).filter _)]

def fastTowerTerm (L d : ℕ) : ℚ :=
  ((primeList L).map (fun p : ℕ =>
    ((min (p ^ (vp p L - vp p d)) (uuF p (vp p L)) : ℕ) : ℚ) / (uuF p (vp p L) : ℚ))).prod

def fastTowerSum (L : ℕ) : ℚ :=
  (((divList L).filter (fun d : ℕ => decide (1 < d) && (primeCount L d != 1))).map
    (fastTowerTerm L)).sum

theorem fastTowerTerm_eq {L d : ℕ} (hL : 0 < L) (hd : d ∣ L) (hd0 : 0 < d) :
    towerTerm L d = fastTowerTerm L d := by
  unfold towerTerm fastTowerTerm
  rw [primeFactors_eq_primeList hL, List.prod_toFinset _ (primeList_nodup hL)]
  congr 1
  apply List.map_congr_left
  intro p hp
  have hp' : p.Prime := by
    rw [primeList, List.mem_filter, isPrimeTD_iff] at hp; exact hp.2
  rcases uuF_eq (L := L) hp' with h | h
  · rw [h, vp_eq_factorization hp' hL, vp_eq_factorization hp' hd0]
  · omega

theorem towerSum_eq {L : ℕ} (hL : 0 < L) : towerSum L = fastTowerSum L := by
  unfold towerSum fastTowerSum
  rw [divisors_eq_divList hL]
  have hfilt : (divList L).toFinset.filter (fun d => 1 < d ∧ ¬ IsPrimePow d)
      = ((divList L).filter (fun d : ℕ => decide (1 < d) && (primeCount L d != 1))).toFinset := by
    rw [List.toFinset_filter]
    apply filter_congr
    intro d hd
    have hdL : d ∣ L := (mem_divList hL d).mp (List.mem_toFinset.mp hd)
    simp only [Bool.and_eq_true, decide_eq_true_iff, bne_iff_ne, ne_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun h => h2 ((isPrimePow_iff_primeCount hL hdL (by omega)).mpr h)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun h => h2 ((isPrimePow_iff_primeCount hL hdL (by omega)).mp h)⟩
  rw [hfilt, List.sum_toFinset _ ((divList_nodup hL).filter _)]
  congr 1
  apply List.map_congr_left
  intro d hd
  rw [List.mem_filter] at hd
  have hdL : d ∣ L := (mem_divList hL d).mp hd.1
  have h1 : 1 < d := by
    have := hd.2; simp only [Bool.and_eq_true, decide_eq_true_iff] at this; exact this.1
  exact fastTowerTerm_eq hL hdL (by omega)

def towerCheck (L : ℕ) : Bool := decide (fastTowerSum L < 1)

theorem no_covering_of_towerCheck {L : ℕ} (h : towerCheck L = true) (S : Finset Cls) :
    ¬ IsCovering L S := by
  intro hS
  have h' : towerSum L < 1 := by
    rw [towerSum_eq hS.pos]; exact of_decide_eq_true h
  exact no_covering_of_towerSum h' S hS

/-! ### Scanning -/

/-- `check2 L`: density test, or tower certificate. -/
def check2 (L : ℕ) : Bool := densCheck L || towerCheck L

theorem no_covering_of_check2 {L : ℕ} (h : check2 L = true) (S : Finset Cls) : ¬ IsCovering L S := by
  unfold check2 at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact no_covering_of_densCheck h S
  · exact no_covering_of_towerCheck h S

/-- Tail-recursive scan: checks every odd `L ∈ (lo, lo + cnt]`. -/
def scanChunk2 (lo : ℕ) : ℕ → Bool
  | 0 => true
  | cnt + 1 => if (lo + 1) % 2 == 0 || check2 (lo + 1) then scanChunk2 (lo + 1) cnt else false

theorem scanChunk2_spec (lo : ℕ) :
    ∀ cnt, scanChunk2 lo cnt = true →
      ∀ L, lo < L → L ≤ lo + cnt → L % 2 = 1 → check2 L = true := by
  intro cnt
  induction cnt generalizing lo with
  | zero => intro _ L h1 h2; omega
  | succ cnt ih =>
    intro h L hlo hle hodd
    unfold scanChunk2 at h
    split_ifs at h with h1
    · rcases Nat.eq_or_lt_of_le hlo with hL | hL
      · subst hL
        rcases Bool.or_eq_true_iff.mp h1 with h1 | h1
        · exfalso; simp at h1; omega
        · exact h1
      · exact ih (lo + 1) h L hL (by omega) hodd

theorem scanChunk2_append (lo : ℕ) :
    ∀ a b, scanChunk2 lo a = true → scanChunk2 (lo + a) b = true → scanChunk2 lo (a + b) = true := by
  intro a
  induction a generalizing lo with
  | zero => intro b _ hb; simpa using hb
  | succ a ih =>
    intro b ha hb
    unfold scanChunk2 at ha
    split_ifs at ha with h1
    · show scanChunk2 lo (a + 1 + b) = true
      rw [show a + 1 + b = (a + b) + 1 by omega]
      unfold scanChunk2
      rw [if_pos h1]
      exact ih (lo + 1) b ha (by rw [show lo + 1 + a = lo + (a + 1) by omega]; exact hb)

theorem odd_covering_lcm_gt_of_scan2 (N : ℕ)
    (hscan : ∀ L, L ≤ N → L % 2 = 1 → check2 L = true)
    (S : Finset Cls) (hgt : ∀ c ∈ S, 1 < c.d) (hodd : ∀ c ∈ S, Odd c.d)
    (hinj : ∀ c ∈ S, ∀ c' ∈ S, c.d = c'.d → c = c') (hcov : CoversZ S) :
    N < S.lcm (·.d) := by
  by_contra hle
  push_neg at hle
  have hS := isCovering_lcm S hgt hinj hcov
  have hoddL := Nat.odd_iff.mp (lcm_odd S hodd)
  exact no_covering_of_check2 (hscan _ hle hoddL) S hS

end Covering
