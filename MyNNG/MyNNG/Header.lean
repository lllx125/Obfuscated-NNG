import Mathlib.Tactic.ApplyAt
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Use
import Mathlib.Tactic.Tauto

-- definition
inductive MyNat where
| zero : MyNat
| succ : MyNat → MyNat

namespace MyNat

instance : Inhabited MyNat where
  default := MyNat.zero

-- addition
opaque add : MyNat → MyNat → MyNat

instance instAdd : Add MyNat where
  add := MyNat.add

@[simp]
axiom add_zero (a : MyNat) : a + zero = a

axiom add_succ (a d : MyNat) : a + (succ d) = succ (a + d)

-- Peano axioms
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

instance : Mul MyNat where
  mul := MyNat.mul

axiom mul_zero (a : MyNat) : a * zero = zero

axiom mul_succ (a b : MyNat) : a * (succ b) = a * b + a

-- some numerals
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

instance : Pow MyNat MyNat where
  pow := pow

axiom pow_zero (m : MyNat) : m ^ zero = one

axiom pow_succ (m n : MyNat) : m ^ (succ n) = m ^ n * m


-- inequality
def le (a b : MyNat) :=  ∃ (c : MyNat), b = a + c

instance : LE MyNat := ⟨MyNat.le⟩

theorem le_iff_exists_add (a b : MyNat) : a ≤ b ↔ ∃ (c : MyNat), b = a + c := Iff.rfl

def lt_myNat (a b : MyNat) := a ≤ b ∧ ¬ (b ≤ a)

instance : LT MyNat := ⟨lt_myNat⟩

theorem lt :  ∀ (a b : MyNat), a < b ↔ a ≤ b ∧ ¬b ≤ a := fun _ _ => Iff.rfl

end MyNat
