/-
Kernel-evaluable arithmetic: divisor enumeration by pairing up to √L, and trial-division
primality, each with a correctness proof relating it to the Mathlib notion.
These are written with structural (fuel) recursion so that `decide` can run them in the kernel.
-/
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Tactic.Ring

namespace Covering

/-- Divisors `e ∈ [m, m+f)` of `L` with `e*e ≤ L`, together with their cofactors `L/e`. -/
def divAux (L : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | f + 1, m =>
    if m * m ≤ L then
      (if L % m == 0 then (if m * m == L then [m] else [m, L / m]) else []) ++ divAux L f (m + 1)
    else []

/-- All divisors of `L` (as a list, possibly with the pairing producing no duplicates). -/
def divList (L : ℕ) : List ℕ := divAux L L 1

theorem mem_divAux_of {L : ℕ} (hL : 0 < L) :
    ∀ (f m e : ℕ), 1 ≤ m → m ≤ e → e < m + f → e * e ≤ L → L % e = 0 →
      e ∈ divAux L f m ∧ L / e ∈ divAux L f m := by
  intro f
  induction f with
  | zero => intro m e _ _ h; omega
  | succ f ih =>
    intro m e hm1 hme hef hee hmod
    unfold divAux
    have hmm : m * m ≤ L := le_trans (Nat.mul_le_mul hme hme) hee
    rw [if_pos hmm]
    rcases Nat.eq_or_lt_of_le hme with rfl | hlt
    · rw [if_pos (by simpa using hmod)]
      by_cases hsq : m * m = L
      · rw [if_pos (by simpa using hsq)]
        have : L / m = m := by
          rw [← hsq]; exact Nat.mul_div_cancel_left m (by omega)
        simp [this]
      · rw [if_neg (by simpa using hsq)]
        simp
    · have := ih (m + 1) e (by omega) hlt (by omega) hee hmod
      simp only [List.mem_append]
      exact ⟨Or.inr this.1, Or.inr this.2⟩

theorem dvd_of_mem_divAux {L : ℕ} (hL : 0 < L) :
    ∀ (f m e : ℕ), 1 ≤ m → e ∈ divAux L f m → e ∣ L := by
  intro f
  induction f with
  | zero => intro m e _ h; simp [divAux] at h
  | succ f ih =>
    intro m e hm he
    unfold divAux at he
    split_ifs at he with h1 h2 h3
    · simp only [List.mem_append, List.mem_singleton] at he
      rcases he with rfl | he
      · exact Nat.dvd_of_mod_eq_zero (by simpa using h2)
      · exact ih (m + 1) e (by omega) he
    · simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
        at he
      rcases he with (rfl | rfl) | he
      · exact Nat.dvd_of_mod_eq_zero (by simpa using h2)
      · exact Nat.div_dvd_of_dvd (Nat.dvd_of_mod_eq_zero (by simpa using h2))
      · exact ih (m + 1) e (by omega) he
    · simp only [List.nil_append] at he
      exact ih (m + 1) e (by omega) he
    · simp at he

theorem mem_divList {L : ℕ} (hL : 0 < L) (e : ℕ) : e ∈ divList L ↔ e ∣ L := by
  constructor
  · exact dvd_of_mem_divAux hL L 1 e le_rfl
  · intro he
    have hepos : 0 < e := Nat.pos_of_dvd_of_pos he hL
    have heL : e ≤ L := Nat.le_of_dvd hL he
    obtain ⟨k, hk⟩ := he
    have hkpos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with rfl | h
      · simp at hk; omega
      · exact h
    have hkL : k ≤ L := by rw [hk]; exact Nat.le_mul_of_pos_left k hepos
    -- either e*e ≤ L or k*k ≤ L
    by_cases hee : e * e ≤ L
    · exact (mem_divAux_of hL L 1 e le_rfl hepos (by omega) hee (by rw [hk]; simp)).1
    · have hkk : k * k ≤ L := by
        by_contra hcon
        push_neg at hee hcon
        have : L * L < (e * e) * (k * k) := Nat.mul_lt_mul'' hee hcon
        have h2 : e * e * (k * k) = (e * k) * (e * k) := by ring
        rw [h2, ← hk] at this
        exact lt_irrefl _ this
      have hmod : L % k = 0 := by rw [hk]; simp
      have := (mem_divAux_of hL L 1 k le_rfl hkpos (by omega) hkk hmod).2
      have hLk : L / k = e := by rw [hk]; exact Nat.mul_div_cancel e hkpos
      rwa [hLk] at this

/-- Invariant: every element `x` of `divAux L f m` divides `L`, and either `x² ≤ L` with `m ≤ x`
(it was visited directly) or `L < x²` with `m ≤ L/x` (it is a cofactor). -/
theorem divAux_inv {L : ℕ} (hL : 0 < L) :
    ∀ (f m x : ℕ), 1 ≤ m → x ∈ divAux L f m →
      x ∣ L ∧ ((x * x ≤ L ∧ m ≤ x) ∨ (L < x * x ∧ m ≤ L / x)) := by
  intro f
  induction f with
  | zero => intro m x _ h; simp [divAux] at h
  | succ f ih =>
    intro m x hm hx
    unfold divAux at hx
    split_ifs at hx with h1 h2 h3
    · simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with rfl | hx
      · exact ⟨Nat.dvd_of_mod_eq_zero (by simpa using h2), Or.inl ⟨h1, le_rfl⟩⟩
      · obtain ⟨hd, hc⟩ := ih (m + 1) x (by omega) hx
        exact ⟨hd, by omega⟩
    · simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil,
        or_false] at hx
      have hmd : m ∣ L := Nat.dvd_of_mod_eq_zero (by simpa using h2)
      have hsq : m * m ≠ L := by simpa using h3
      rcases hx with (rfl | rfl) | hx
      · exact ⟨hmd, Or.inl ⟨h1, le_rfl⟩⟩
      · refine ⟨Nat.div_dvd_of_dvd hmd, Or.inr ⟨?_, ?_⟩⟩
        · -- L < (L/m)^2 since m*m < L
          have hlt : m * m < L := lt_of_le_of_ne h1 hsq
          have hq : L = m * (L / m) := (Nat.mul_div_cancel' hmd).symm
          have hpos : 0 < L / m := Nat.div_pos (Nat.le_of_dvd hL hmd) (by omega)
          by_contra hcon
          push_neg at hcon
          -- (L/m)*(L/m) ≤ L = m*(L/m) ⇒ L/m ≤ m ⇒ L = m*(L/m) ≤ m*m, contradiction
          have h5 : L / m ≤ m := by
            have : L / m * (L / m) ≤ m * (L / m) := by rw [← hq]; exact hcon
            exact Nat.le_of_mul_le_mul_right this hpos
          have : L ≤ m * m := by rw [hq]; exact Nat.mul_le_mul_left m h5
          omega
        · rw [Nat.div_div_self hmd hL.ne']
      · obtain ⟨hd, hc⟩ := ih (m + 1) x (by omega) hx
        exact ⟨hd, by omega⟩
    · simp only [List.nil_append] at hx
      obtain ⟨hd, hc⟩ := ih (m + 1) x (by omega) hx
      exact ⟨hd, by omega⟩
    · simp at hx

theorem divAux_nodup {L : ℕ} (hL : 0 < L) :
    ∀ (f m : ℕ), 1 ≤ m → (divAux L f m).Nodup := by
  intro f
  induction f with
  | zero => intro m _; simp [divAux]
  | succ f ih =>
    intro m hm
    unfold divAux
    have ihm := ih (m + 1) (by omega)
    have inv := divAux_inv hL f (m + 1)
    split_ifs with h1 h2 h3
    · -- [m] ++ rest
      rw [List.singleton_append, List.nodup_cons]
      refine ⟨fun hx => ?_, ihm⟩
      obtain ⟨_, hc⟩ := inv m (by omega) hx
      rcases hc with ⟨_, h⟩ | ⟨h, _⟩
      · omega
      · omega
    · -- [m, L/m] ++ rest
      have hmd : m ∣ L := Nat.dvd_of_mod_eq_zero (by simpa using h2)
      have hsq : m * m ≠ L := by simpa using h3
      have hlt : m * m < L := lt_of_le_of_ne h1 hsq
      have hq : L = m * (L / m) := (Nat.mul_div_cancel' hmd).symm
      have hpos : 0 < L / m := Nat.div_pos (Nat.le_of_dvd hL hmd) (by omega)
      have hmlt : m < L / m := by
        by_contra hcon; push_neg at hcon
        have : L ≤ m * m := by rw [hq]; exact Nat.mul_le_mul_left m hcon
        omega
      rw [List.cons_append, List.singleton_append, List.nodup_cons, List.nodup_cons]
      refine ⟨?_, ?_, ihm⟩
      · intro hx
        simp only [List.mem_cons] at hx
        rcases hx with h | hx
        · omega
        · obtain ⟨_, hc⟩ := inv m (by omega) hx
          rcases hc with ⟨_, h⟩ | ⟨h, _⟩ <;> omega
      · intro hx
        obtain ⟨_, hc⟩ := inv (L / m) (by omega) hx
        rcases hc with ⟨h, h'⟩ | ⟨_, h'⟩
        · -- (L/m)*(L/m) ≤ L forces L/m ≤ m
          have h5 : L / m ≤ m := by
            have : L / m * (L / m) ≤ m * (L / m) := by rw [← hq]; exact h
            exact Nat.le_of_mul_le_mul_right this hpos
          omega
        · rw [Nat.div_div_self hmd hL.ne'] at h'
          omega
    · simpa using ihm
    · simp

theorem divList_nodup {L : ℕ} (hL : 0 < L) : (divList L).Nodup := divAux_nodup hL L 1 le_rfl

theorem divisors_eq_divList {L : ℕ} (hL : 0 < L) : Nat.divisors L = (divList L).toFinset := by
  ext e
  rw [Nat.mem_divisors, List.mem_toFinset, mem_divList hL]
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, hL.ne'⟩

/-! ### Trial-division primality -/

/-- `tdAux p f m = true` iff no `e ∈ [m, m+f)` with `e*e ≤ p` divides `p`. -/
def tdAux (p : ℕ) : ℕ → ℕ → Bool
  | 0, _ => true
  | f + 1, m => if m * m ≤ p then (p % m != 0) && tdAux p f (m + 1) else true

def isPrimeTD (p : ℕ) : Bool := 2 ≤ p && tdAux p p 2

theorem tdAux_spec (p : ℕ) :
    ∀ (f m : ℕ), tdAux p f m = true ↔ ∀ e, m ≤ e → e < m + f → e * e ≤ p → ¬ e ∣ p := by
  intro f
  induction f with
  | zero =>
    intro m; simp [tdAux]
    intro e h1 h2; omega
  | succ f ih =>
    intro m
    unfold tdAux
    by_cases hmm : m * m ≤ p
    · rw [if_pos hmm, Bool.and_eq_true, ih (m + 1), bne_iff_ne, ne_eq]
      constructor
      · rintro ⟨h1, h2⟩ e hme hef hee
        rcases Nat.eq_or_lt_of_le hme with rfl | hlt
        · intro hd; exact h1 (Nat.mod_eq_zero_of_dvd hd)
        · exact h2 e hlt (by omega) hee
      · intro h
        refine ⟨fun hmod => h m le_rfl (by omega) hmm (Nat.dvd_of_mod_eq_zero hmod), ?_⟩
        intro e hme hef hee
        exact h e (by omega) (by omega) hee
    · rw [if_neg hmm]
      simp only [true_iff]
      intro e hme _ hee
      exfalso
      exact hmm (le_trans (Nat.mul_le_mul hme hme) hee)

theorem isPrimeTD_iff (p : ℕ) : isPrimeTD p = true ↔ p.Prime := by
  unfold isPrimeTD
  rw [Bool.and_eq_true, decide_eq_true_iff, tdAux_spec, Nat.prime_def_le_sqrt]
  constructor
  · rintro ⟨h2, h⟩
    refine ⟨h2, fun m hm hms => h m hm ?_ (Nat.le_sqrt.mp hms)⟩
    have := Nat.sqrt_le_self p
    omega
  · rintro ⟨h2, h⟩
    refine ⟨h2, fun e he _ hee => h e he (Nat.le_sqrt.mpr hee)⟩

/-- The primes dividing `L`, computed. -/
def primeList (L : ℕ) : List ℕ := (divList L).filter isPrimeTD

theorem primeFactors_eq_primeList {L : ℕ} (hL : 0 < L) :
    L.primeFactors = (primeList L).toFinset := by
  ext p
  rw [Nat.mem_primeFactors, List.mem_toFinset, primeList, List.mem_filter, mem_divList hL,
    isPrimeTD_iff]
  constructor
  · exact fun h => ⟨h.2.1, h.1⟩
  · exact fun h => ⟨h.2, h.1, hL.ne'⟩

theorem primeList_nodup {L : ℕ} (hL : 0 < L) : (primeList L).Nodup :=
  (divList_nodup hL).filter _

end Covering
