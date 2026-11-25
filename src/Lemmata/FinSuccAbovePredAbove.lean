module

public import Mathlib.Data.Fin.SuccPred

@[expose] public section

theorem Fin.val_succAbove_eq_ite {n : ℕ} (q : Fin (n + 1)) (j : Fin n) :
    ((q.succAbove j : Fin (n + 1)) : ℕ) = if (j : ℕ) < q then (j : ℕ) else (j : ℕ) + 1 := by
  by_cases h : (j : ℕ) < q
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by simpa [Fin.lt_def] using h)]
    simp [h]
  · rw [Fin.succAbove_of_le_castSucc _ _ (by simp [Fin.le_def]; omega)]
    simp [h]

theorem Fin.val_predAbove_eq_ite {n : ℕ} (i : Fin n) (x : Fin (n + 1)) :
    ((Fin.predAbove i x : Fin n) : ℕ) = if (i : ℕ) < x then (x : ℕ) - 1 else x := by
  unfold Fin.predAbove
  simp only [Fin.lt_def, Fin.val_castSucc]
  split_ifs <;> simp
