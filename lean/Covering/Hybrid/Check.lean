/-
Decidable form of the distorted tower certificate.
-/
import Covering.Hybrid.Main
import Covering.Fast

namespace Covering.Hybrid

open Finset

def validB : List Stage → Bool
  | [] => true
  | s :: rs => isPrimeTD s.p && decide (1 ≤ s.e) && decide (0 ≤ s.δ) && decide (s.δ ≤ 1 / 2) &&
      decide ((Qs rs).Coprime s.p) && validB rs

theorem validB_spec : ∀ rs : List Stage, validB rs = true → Valid rs
  | [], _ => trivial
  | s :: rs, h => by
    simp only [validB, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
    exact ⟨(isPrimeTD_iff _).mp h1, h2, h3, h4, h5, validB_spec rs h6⟩

/-- The certificate check for one modulus `L` with stages `rs`. -/
def hyb (L : ℕ) (rs : List Stage) : Bool :=
  Qs rs == L && validB rs && decide (eta rs < 1)

theorem no_covering_of_hyb {L : ℕ} {rs : List Stage} (h : hyb L rs = true) (S : Finset Cls) :
    ¬ IsCovering L S := by
  intro hS
  simp only [hyb, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨hQ, hv⟩, heta⟩ := h
  have hv' := validB_spec rs hv
  have hF : Fam (Qs rs) S := ⟨fun c hc => hQ ▸ hS.dvd c hc, hS.gt, hS.inj⟩
  have := one_le_eta hv' hF (fun n hn => hS.cov n (hQ ▸ hn))
  linarith

end Covering.Hybrid
