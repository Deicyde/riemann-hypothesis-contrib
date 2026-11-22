import Mathlib.Data.ENat.Basic

namespace ReciprocityTheory.ChartRestriction.G.Geo

theorem withBot_eq_of_add_one {a : WithBot ℕ∞} {n : ℕ}
    (h : a + 1 = ((n + 1 : ℕ) : WithBot ℕ∞)) : a = (n : WithBot ℕ∞) := by
  induction a using WithBot.recBotCoe with
  | bot =>
    rw [WithBot.bot_add] at h
    exact absurd h.symm (by simp)
  | coe b =>
    induction b using ENat.recTopCoe with
    | top =>
      simp at h
      exact absurd h.symm (fun h2 => ENat.coe_ne_top n (WithBot.coe_injective
        (show ((n : ℕ∞) : WithBot ℕ∞) = ((⊤ : ℕ∞) : WithBot ℕ∞) from h2)))
    | coe k =>
      have h' : ((k + 1 : ℕ) : WithBot ℕ∞) = ((n + 1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast h
      have h2 : k + 1 = n + 1 := by exact_mod_cast h'
      have hk : k = n := by omega
      subst hk
      norm_cast

end ReciprocityTheory.ChartRestriction.G.Geo
