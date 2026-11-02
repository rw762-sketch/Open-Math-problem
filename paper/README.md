# A tower sieve certificate for the lcm of an odd covering system, checked in Lean

**Ryan Wu and Claude Fable 5.1** · November 2026 · draft v0.1

[PDF](main.pdf) · [LaTeX source](main.tex) · [progress page with claims ledger](../docs/PROGRESS.md)

## Abstract

A covering system is a finite family of residue classes whose union is ℤ. Erdős and Selfridge asked whether one can have all moduli odd, distinct, and greater than one; the question is open. We give an elementary necessary condition on the lcm L of the moduli (the tower certificate T(L) ≥ 1), sharp at L = 12 and 80, prove it sound in Lean 4, and certify that every odd distinct covering has L > 10⁵ with the proof kernel alone and L > 6 891 884 with compiled evaluation. The certificate sharpens the 1986 Berger–Felzenbaum–Fraenkel condition, which is its exponent-free limit. We place it against Mian–Siddique, Hackmon, McNew–Setty and Schroeder, stating for each claim whether it is proved, machine-checked, numerical, or unchecked.

Rebuild: `latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex`.
