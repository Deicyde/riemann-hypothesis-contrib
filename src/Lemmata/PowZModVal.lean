module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.ZMod.Basic

@[expose] public section

theorem ZMod.pow_val_add_of_pow_eq_one {Ω : Type} [Field Ω] {n : ℕ} [NeZero n] {ζ : Ω} (h : ζ ^ n = 1) (a b : ZMod n) :
    ζ ^ (a + b).val = ζ ^ a.val * ζ ^ b.val := by
  rw [ZMod.val_add, ← pow_add]
  conv_rhs => rw [← Nat.mod_add_div (a.val + b.val) n, pow_add, pow_mul, h, one_pow, mul_one]
