module

public import Mathlib

@[expose] public section

namespace GlobalTheory.Published

def primesInProgression (a q : ℕ) : Set ℕ := {p | p.Prime ∧ p ≡ a [MOD q]}

noncomputable def leastPrimeMod (a q : ℕ) : ℕ := sInf (primesInProgression a q)

/-- **Linnik's theorem**, in its qualitative form: there are positive constants `C` and `L` such
that, for all coprime `a, q ≥ 1`, the least prime congruent to `a` modulo `q` is at most
`C * q ^ L`. No value of `L` and no effectivity of the constants is asserted.

The theorem is due to
[U. V. Linnik, *On the least prime in an arithmetic progression. I. The basic theorem*][linnik1944].
It is recalled in this form, with effective constants, in
[T. Xylouris, *On Linnik's constant* (equation (1.5))][xylouris2009], which proves the bound with
`L = 5.2` (Theorem 1.1). Linnik's paper was not read in preparing this reference. This reference
is a reader's proposal and has not been checked by a mathematician. -/
@[wikidata Q2703389]
def Linnik : Prop :=
  ∃ C L : ℝ, 0 < C ∧ 0 < L ∧ ∀ a q : ℕ, 1 ≤ a → 1 ≤ q → a.Coprime q →
    (leastPrimeMod a q : ℝ) ≤ C * (q : ℝ) ^ L

private theorem exists_prime_modEq_of_coprime (a q : ℕ) (hq : 1 ≤ q) (h : a.Coprime q) :
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] := by
  haveI : NeZero q := ⟨by omega⟩
  have hu : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).2 h
  obtain ⟨p, -, hp, hpa⟩ := Nat.forall_exists_prime_gt_and_eq_mod hu 0
  exact ⟨p, hp, (ZMod.natCast_eq_natCast_iff p a q).1 hpa⟩

theorem _root_.GlobalTheory.Published.linnik_iff_exists_prime : _root_.GlobalTheory.Published.Linnik ↔
    ∃ C L : ℝ, 0 < C ∧ 0 < L ∧ ∀ a q : ℕ, 1 ≤ a → 1 ≤ q → a.Coprime q →
      ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ C * (q : ℝ) ^ L := by
  constructor
  · rintro ⟨C, L, hC, hL, hb⟩
    refine ⟨C, L, hC, hL, fun a q ha hq h => ?_⟩
    have hne : (_root_.GlobalTheory.Published.primesInProgression a q).Nonempty :=
      exists_prime_modEq_of_coprime a q hq h
    have hmem := Nat.sInf_mem hne
    exact ⟨_, hmem.1, hmem.2, hb a q ha hq h⟩
  · rintro ⟨C, L, hC, hL, hb⟩
    refine ⟨C, L, hC, hL, fun a q ha hq h => ?_⟩
    obtain ⟨p, hp, hpa, hpC⟩ := hb a q ha hq h
    have hle : _root_.GlobalTheory.Published.leastPrimeMod a q ≤ p := Nat.sInf_le ⟨hp, hpa⟩
    exact le_trans (by exact_mod_cast hle) hpC

end GlobalTheory.Published
