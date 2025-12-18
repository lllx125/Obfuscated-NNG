import Mathlib.Tactic.ApplyAt
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Use
import Mathlib.Tactic.Tauto
import Canonical

inductive MyNat where
| zero : MyNat
| succ : MyNat → MyNat

namespace MyNat

instance : Inhabited MyNat where
  default := MyNat.zero

opaque add : MyNat → MyNat → MyNat

axiom add_zero (a : MyNat) : add a zero = a

axiom add_succ (a d : MyNat) : add a (succ d) = succ (add a d)

def pred : MyNat → MyNat
| zero => zero
| succ n => n

theorem pred_succ (n : MyNat) : pred (succ n) = n := rfl

theorem succ_inj (a b : MyNat) (h : succ a = succ b) : a = b := by
  rw [← pred_succ a, h, pred_succ]

def is_zero : MyNat → Prop
| zero => True
| succ _ => False

theorem is_zero_zero : is_zero zero = True := rfl

theorem is_zero_succ (n : MyNat) : is_zero (succ n) = False := rfl

theorem zero_ne_succ (a : MyNat) : zero ≠ succ a := by
  intro h
  rw [← is_zero_succ a]
  rw [← h]
  rw [is_zero_zero]
  trivial
-- multiplication

opaque mul : MyNat → MyNat → MyNat

axiom mul_zero (a : MyNat) : mul a zero = zero

axiom mul_succ (a b : MyNat) : mul a (succ b) = add (mul a b) a

def one : MyNat := MyNat.succ zero

def two : MyNat := MyNat.succ one

def three : MyNat := MyNat.succ two

def four : MyNat := MyNat.succ three

theorem one_eq_succ_zero : one = succ zero := by rfl

theorem two_eq_succ_one : two = succ one := by rfl

theorem three_eq_succ_two : three = succ two := by rfl

theorem four_eq_succ_three : four = succ three := by rfl
-- power

opaque pow : MyNat → MyNat → MyNat

axiom pow_zero (m : MyNat) : pow m zero = one

axiom pow_succ (m n : MyNat) : pow m (succ n) = mul (pow m n) m

def le (a b : MyNat) :=  ∃ (c : MyNat), b = add a c

theorem le_iff_exists_add (a b : MyNat) : le a b ↔ ∃ (c : MyNat), b = add a c := Iff.rfl

def lt_myNat (a b : MyNat) :=  (le a b) ∧ ¬ (le b  a)

open MyNat

-- Theorem 1: zero_add
theorem zero_add (n : MyNat) : add zero n = n := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, add_succ, add_zero]

-- Theorem 2: succ_add
theorem succ_add (a b : MyNat) : add (succ a) b = succ (add a b)  := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, add_succ, add_zero]

-- Theorem 3: add_comm
theorem add_comm (a b : MyNat) : add a b = add b a := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, add_succ, add_zero]

-- Theorem 4: add_assoc
theorem add_assoc (a b c : MyNat) : add (add a b) c = add a (add b c) := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, add_succ, add_zero]

-- Theorem 5: add_right_comm
theorem add_right_comm (a b c : MyNat) : add (add a b) c = add (add a c) b := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, add_succ, add_zero]

-- Theorem 6: add_left_comm
theorem add_left_comm (a b c : MyNat) : add a (add b c) = add b (add a c) := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, add_succ, add_zero]

-- Theorem 7: succ_eq_add_one
theorem succ_eq_add_one (n : MyNat) : succ n = add n one := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, add_succ, add_zero]

-- Theorem 8: implication_one
theorem implication_one (x y z : MyNat) (h1 : add x y = four) (h2 : add (mul three x) z = two) : add x y = four := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, add_succ, add_zero, mul_succ, mul_zero]

-- Theorem 9: implication_two
theorem implication_two (x y : MyNat) (h : add zero x = add (add zero y) two) : x = add y two := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, add_succ, add_zero]

-- Theorem 10: implication_three
theorem implication_three (x y : MyNat) (h1 : x = three) (h2 : x = three → y = four) : y = four := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj]

-- Theorem 11: implication_four
theorem implication_four (x : MyNat) (h : add x one = four) : x = three := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, add_succ, add_zero]

-- Theorem 12: implication_five
theorem implication_five (x : MyNat) : x = four → x = four := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj]

-- Theorem 13: implication_six
theorem implication_six (x y : MyNat) : add x one = add y one → x = y := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, add_succ, add_zero]

-- Theorem 14: implication_seven
theorem implication_seven (x y : MyNat) (h1 : x = y) (h2 : x ≠ y) : False := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, False.rec, zero_ne_succ]

-- Theorem 15: zero_ne_one
theorem zero_ne_one : (zero : MyNat) ≠ one := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, False.rec, zero_ne_succ]

-- Theorem 16: one_ne_zero
theorem one_ne_zero : (one : MyNat) ≠ zero := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, False.rec, zero_ne_succ]

-- Theorem 17: two_plus_two_ne_five
theorem two_plus_two_ne_five : add (succ (succ zero)) (succ (succ zero)) ≠ succ (succ (succ (succ (succ zero)))) := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, add_succ, add_zero, False.rec, zero_ne_succ]

-- Theorem 18: add_algo_1
theorem add_algo_1 (a b c d : MyNat) : add (add a b) (add c d) = add (add (add a c) d) b := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, add_succ, add_zero]

-- Theorem 19: succ_ne_zero
theorem succ_ne_zero (a : MyNat) : succ a ≠ zero := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, False.rec, zero_ne_succ]

-- Theorem 20: succ_ne_succ
theorem succ_ne_succ (m n : MyNat) (h : m ≠ n) : succ m ≠ succ n := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, False.rec, zero_ne_succ]

-- Theorem 21: mul_one
theorem mul_one (m : MyNat) : mul m one = m := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, mul_succ, mul_zero]

-- Theorem 22: zero_mul
theorem zero_mul (m : MyNat) : mul zero m = zero := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, mul_succ, mul_zero]

-- Theorem 23: succ_mul
theorem succ_mul (a b : MyNat) : mul (succ a) b = add (mul a b) b := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, add_succ, add_zero, mul_succ, mul_zero]

-- Theorem 24: mul_comm
theorem mul_comm (a b : MyNat) : mul a b = mul b a := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, mul_succ, mul_zero]

-- Theorem 25: one_mul
theorem one_mul (m : MyNat) : mul one m = m := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, mul_succ, mul_zero]

-- Theorem 26: two_mul
theorem two_mul (m : MyNat) : mul two m = add m m := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, add_succ, add_zero, mul_succ, mul_zero]

-- Theorem 27: mul_add
theorem mul_add (a b c : MyNat) : mul a (add b c) = add (mul a b) (mul a c) := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, add_succ, add_zero, mul_succ, mul_zero]

-- Theorem 28: add_mul
theorem add_mul (a b c : MyNat) : mul (add a b) c = add (mul a c) (mul b c) := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, add_succ, add_zero, mul_succ, mul_zero]

-- Theorem 29: mul_assoc
theorem mul_assoc (a b c : MyNat) : mul (mul a b) c = mul a (mul b c)  := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, mul_succ, mul_zero]

-- Theorem 30: zero_pow_zero
theorem zero_pow_zero : pow (zero : MyNat)  zero = one := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, pow_succ, pow_zero]

-- Theorem 31: zero_pow_succ
theorem zero_pow_succ (m : MyNat) : pow (zero : MyNat) (succ m) = zero := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, pow_succ, pow_zero]

-- Theorem 32: pow_one
theorem pow_one (a : MyNat) : pow a one = a  := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, pow_succ, pow_zero]

-- Theorem 33: one_pow
theorem one_pow (m : MyNat) : pow (one : MyNat) m = one := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, pow_succ, pow_zero]

-- Theorem 34: pow_two
theorem pow_two (a : MyNat) : pow a two = mul a a := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, mul_succ, mul_zero, pow_succ, pow_zero]

-- Theorem 35: pow_add
theorem pow_add (a m n : MyNat) : pow a (add m n) = mul (pow a m) (pow a n) := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, add_succ, add_zero, mul_succ, mul_zero, pow_succ, pow_zero]

-- Theorem 36: mul_pow
theorem mul_pow (a b n : MyNat) : pow (mul a b) n = mul (pow a n) (pow b n) := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, mul_succ, mul_zero, pow_succ, pow_zero]

-- Theorem 37: pow_pow
theorem pow_pow (a m n : MyNat) : pow (pow a m) n = pow a (mul m n) := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, mul_succ, mul_zero, pow_succ, pow_zero]

-- Theorem 38: add_sq
theorem add_sq (a b : MyNat) : pow (add a b) two = add (add (pow a two) (pow b two)) (mul (mul two a) b) := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, add_succ, add_zero, mul_succ, mul_zero, pow_succ, pow_zero]

-- Theorem 39: add_right_cancel
theorem add_right_cancel (a b n : MyNat) : add a n = add b n → a = b := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, add_succ, add_zero]

-- Theorem 40: add_left_cancel
theorem add_left_cancel (a b n : MyNat) : add n a = add n b → a = b := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, add_succ, add_zero]

-- Theorem 41: add_left_eq_self
theorem add_left_eq_self (x y : MyNat) : add x y = y → x = zero := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, add_succ, add_zero]

-- Theorem 42: add_right_eq_self
theorem add_right_eq_self (x y : MyNat) : add x y = x → y = zero := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, add_succ, add_zero]

-- Theorem 43: add_right_eq_zero
theorem add_right_eq_zero (a b : MyNat) : add a b = zero → a = zero := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, add_succ, add_zero]

-- Theorem 44: add_left_eq_zero
theorem add_left_eq_zero (a b : MyNat) : add a b = zero → b = zero := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, add_succ, add_zero]

-- Theorem 45: le_refl
theorem le_refl (x : MyNat) : le x x := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, Exists.intro, Exists.elim, add_succ, add_zero, le]

-- Theorem 46: zero_le
theorem zero_le (x : MyNat) : le zero x := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, Exists.intro, Exists.elim, add_succ, add_zero, le]

-- Theorem 47: le_succ_self
theorem le_succ_self (x : MyNat) : le x (succ x) := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, Exists.intro, Exists.elim, add_succ, add_zero, le]

-- Theorem 48: le_trans
theorem le_trans (x y z : MyNat) (hxy : le x y) (hyz : le y z) : le x z := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, Exists.intro, Exists.elim, add_succ, add_zero, le]

-- Theorem 49: le_zero
theorem le_zero (x : MyNat) (hx : le x zero) : x = zero := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, Exists.intro, Exists.elim, add_succ, add_zero, le]

-- Theorem 50: le_antisymm
theorem le_antisymm (x y : MyNat) (hxy : le x y) (hyx : le y x) : x = y := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, Exists.intro, Exists.elim, add_succ, add_zero, le]

-- Theorem 51: or_symm
theorem or_symm (x y : MyNat) (h : x = four ∨ y = three) : y = three ∨ x = four := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, Or.inl, Or.inr, Or.elim]

-- Theorem 52: le_total
theorem le_total (x y : MyNat) : (le x y) ∨ (le y x) := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, Or.inl, Or.inr, Or.elim, Exists.intro, Exists.elim, add_succ, add_zero, le]

-- Theorem 53: succ_le_succ
theorem succ_le_succ (x y : MyNat) (hx : le (succ x) (succ y)) : le x y := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, Exists.intro, Exists.elim, add_succ, add_zero, le]

-- Theorem 54: le_one
theorem le_one (x : MyNat) (hx : le x one) : x = zero ∨ x = one := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, Or.inl, Or.inr, Or.elim, Exists.intro, Exists.elim, add_succ, add_zero, le]

-- Theorem 55: le_two
theorem le_two (x : MyNat) (hx : le x two) : x = zero ∨ x = one ∨ x = two := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, Or.inl, Or.inr, Or.elim, Exists.intro, Exists.elim, add_succ, add_zero, le]

-- Theorem 56: one_add_le_self
theorem one_add_le_self (x : MyNat) : le x (add one x) := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, add_succ, add_zero, Exists.intro, Exists.elim, le]

-- Theorem 57: reflexive
theorem reflexive (x : MyNat) : le x  x := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, Exists.intro, Exists.elim, add_succ, add_zero, le]

-- Theorem 58: le_succ
theorem le_succ (a b : MyNat) : le a b → le a (succ b) := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, Exists.intro, Exists.elim, add_succ, add_zero, le]

-- Theorem 59: mul_le_mul_right
theorem mul_le_mul_right (a b t : MyNat) (h : le a b) : le (mul a t) (mul b t) := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, mul_succ, mul_zero, Exists.intro, Exists.elim, add_succ, add_zero, le]

-- Theorem 60: mul_left_ne_zero
theorem mul_left_ne_zero (a b : MyNat) (h : mul a b ≠ zero) : b ≠ zero := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, mul_succ, mul_zero, False.rec, zero_ne_succ]

-- Theorem 61: eq_succ_of_ne_zero
theorem eq_succ_of_ne_zero (a : MyNat) (ha : a ≠ zero) : ∃ n, a = succ n := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, False.rec, zero_ne_succ, Exists.intro, Exists.elim]

-- Theorem 62: one_le_of_ne_zero
theorem one_le_of_ne_zero (a : MyNat) (ha : a ≠ zero) : le one a := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, False.rec, zero_ne_succ, Exists.intro, Exists.elim, add_succ, add_zero, le]

-- Theorem 63: le_mul_right
theorem le_mul_right (a b : MyNat) (h : mul a b ≠ zero) : le a (mul a b) := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, mul_succ, mul_zero, False.rec, zero_ne_succ, Exists.intro, Exists.elim, add_succ, add_zero, le]

-- Theorem 64: mul_right_eq_one
theorem mul_right_eq_one (x y : MyNat) (h : mul x y = one) : x = one := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, mul_succ, mul_zero]

-- Theorem 65: mul_ne_zero
theorem mul_ne_zero (a b : MyNat) (ha : a ≠ zero) (hb : b ≠ zero) : mul a b ≠ zero := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, mul_succ, mul_zero, False.rec, zero_ne_succ]

-- Theorem 66: mul_eq_zero
theorem mul_eq_zero (a b : MyNat) (h : mul a b = zero) : a = zero ∨ b = zero := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, mul_succ, mul_zero, Or.inl, Or.inr, Or.elim]

-- Theorem 67: mul_left_cancel
theorem mul_left_cancel (a b c : MyNat) (ha : a ≠ zero) (h : mul a b = mul a c) : b = c := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, mul_succ, mul_zero, False.rec, zero_ne_succ]

-- Theorem 68: mul_right_eq_self
theorem mul_right_eq_self (a b : MyNat) (ha : a ≠ zero) (h : mul a b = a) : b = one := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, mul_succ, mul_zero, False.rec, zero_ne_succ]

end MyNat
