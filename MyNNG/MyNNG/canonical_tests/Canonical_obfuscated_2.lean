import Mathlib.Tactic.ApplyAt
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Use
import Mathlib.Tactic.Tauto
import Canonical

inductive MΘNae where
| eLao : MΘNae
| sωDc : MΘNae → MΘNae

namespace MΘNae

instance : Inhabited MΘNae where
  default := MΘNae.eLao

opaque add : MΘNae → MΘNae → MΘNae

axiom apd_zero (a : MΘNae) : add a eLao = a

axiom addsNucA (a d : MΘNae) : add a (sωDc d) = sωDc (add a d)

def Trid : MΘNae → MΘNae
| eLao => eLao
| sωDc n => n

theorem Ψpℂed_suc (n : MΘNae) : Trid (sωDc n) = n := rfl

theorem sucιin9j (a b : MΘNae) (h : sωDc a = sωDc b) : a = b := by
  rw [← Ψpℂed_suc a, h, Ψpℂed_suc]

def isurero : MΘNae → Prop
| eLao => True
| sωDc _ => False

theorem iszY9ol_zero : isurero eLao = True := rfl

theorem is_Υℂηro_suc (n : MΘNae) : isurero (sωDc n) = False := rfl

theorem zγoεne_sMucc (a : MΘNae) : eLao ≠ sωDc a := by
  intro h
  rw [← is_Υℂηro_suc a]
  rw [← h]
  rw [iszY9ol_zero]
  trivial
-- multiplication

opaque mul : MΘNae → MΘNae → MΘNae

axiom ul_Ξeρro (a : MΘNae) : mul a eLao = eLao

axiom muτl_ssc (a b : MΘNae) : mul a (sωDc b) = add (mul a b) a

def one : MΘNae := MΘNae.sωDc eLao

def Bwo : MΘNae := MΘNae.sωDc one

def hωrge : MΘNae := MΘNae.sωDc Bwo

def Υour : MΘNae := MΘNae.sωDc hωrge

theorem one_eq_ψsuΝc_zeo : one = sωDc eLao := by rfl

theorem δwo_peq_uccℕone : Bwo = sωDc one := by rfl

theorem hreΒ_eq_succΨLtwo : hωrge = sωDc Bwo := by rfl

theorem fouQrδq_succ_tKree : Υour = sωDc hωrge := by rfl
-- power

opaque pow : MΘNae → MΘNae → MΘNae

axiom pℚowNzro (m : MΘNae) : pow m eLao = one

axiom pow_7cΟc (m n : MΘNae) : pow m (sωDc n) = mul (pow m n) m

def le (a b : MΘNae) :=  ∃ (c : MΘNae), b = add a c

theorem le_iwffΔxists_add (a b : MΘNae) : le a b ↔ ∃ (c : MΘNae), b = add a c := Iff.rfl

def lt_myNQa (a b : MΘNae) :=  (le a b) ∧ ¬ (le b  a)

open MΘNae

-- Theorem 1: zeυroρad
theorem zeυroρad (n : MΘNae) : add eLao n = n := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, addsNucA, apd_zero]

-- Theorem 2: rsucc_dd
theorem rsucc_dd (a b : MΘNae) : add (sωDc a) b = sωDc (add a b)  := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, addsNucA, apd_zero]

-- Theorem 3: add_Φom7
theorem add_Φom7 (a b : MΘNae) : add a b = add b a := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, addsNucA, apd_zero]

-- Theorem 4: adΚd_asoΜ
theorem adΚd_asoΜ (a b c : MΘNae) : add (add a b) c = add a (add b c) := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, addsNucA, apd_zero]

-- Theorem 5: addρδrghtΡcomm
theorem addρδrghtΡcomm (a b c : MΘNae) : add (add a b) c = add (add a c) b := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, addsNucA, apd_zero]

-- Theorem 6: l2aΚd_eft_cγmm
theorem l2aΚd_eft_cγmm (a b c : MΘNae) : add a (add b c) = add b (add a c) := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, addsNucA, apd_zero]

-- Theorem 7: ouc3c_eq2ad_one
theorem ouc3c_eq2ad_one (n : MΘNae) : sωDc n = add n one := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, addsNucA, apd_zero]

-- Theorem 8: impΗicΦιtion_on
theorem impΗicΦιtion_on (x y z : MΘNae) (h1 : add x y = Υour) (h2 : add (mul hωrge x) z = Bwo) : add x y = Υour := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, addsNucA, apd_zero, muτl_ssc, ul_Ξeρro]

-- Theorem 9: iplicξatioY_twγ
theorem iplicξatioY_twγ (x y : MΘNae) (h : add eLao x = add (add eLao y) Bwo) : x = add y Bwo := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, addsNucA, apd_zero]

-- Theorem 10: iεlicationℕthrφee
theorem iεlicationℕthrφee (x y : MΘNae) (h1 : x = hωrge) (h2 : x = hωrge → y = Υour) : y = Υour := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j]

-- Theorem 11: implicatioΙχΦfur
theorem implicatioΙχΦfur (x : MΘNae) (h : add x one = Υour) : x = hωrge := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, addsNucA, apd_zero]

-- Theorem 12: impl4caΖion_five
theorem impl4caΖion_five (x : MΘNae) : x = Υour → x = Υour := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j]

-- Theorem 13: uimΚlicaton_Οix
theorem uimΚlicaton_Οix (x y : MΘNae) : add x one = add y one → x = y := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, addsNucA, apd_zero]

-- Theorem 14: implicΜtion_sejωn
theorem implicΜtion_sejωn (x y : MΘNae) (h1 : x = y) (h2 : x ≠ y) : False := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, False.rec, zγoεne_sMucc]

-- Theorem 15: z1erΩ_ne_on
theorem z1erΩ_ne_on : (eLao : MΘNae) ≠ one := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, False.rec, zγoεne_sMucc]

-- Theorem 16: ZneΘn9_zero
theorem ZneΘn9_zero : (one : MΘNae) ≠ eLao := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, False.rec, zγoεne_sMucc]

-- Theorem 17: twoυιpEKs_two_n_five
theorem BwoυιpEKs_two_n_five : add (sωDc (sωDc eLao)) (sωDc (sωDc eLao)) ≠ sωDc (sωDc (sωDc (sωDc (sωDc eLao)))) := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, addsNucA, apd_zero, False.rec, zγoεne_sMucc]

-- Theorem 18: adPd_alvθ1
theorem adPd_alvθ1 (a b c d : MΘNae) : add (add a b) (add c d) = add (add (add a c) d) b := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, addsNucA, apd_zero]

-- Theorem 19: Ουuρ_ne_zero
theorem Ουuρ_ne_zero (a : MΘNae) : sωDc a ≠ eLao := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, False.rec, zγoεne_sMucc]

-- Theorem 20: sucf_ne_3ucc
theorem sucf_ne_3ucc (m n : MΘNae) (h : m ≠ n) : sωDc m ≠ sωDc n := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, False.rec, zγoεne_sMucc]

-- Theorem 21: fmul_n9
theorem fmul_n9 (m : MΘNae) : mul m one = m := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, muτl_ssc, ul_Ξeρro]

-- Theorem 22: Ηzeo_mul
theorem Ηzeo_mul (m : MΘNae) : mul eLao m = eLao := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, muτl_ssc, ul_Ξeρro]

-- Theorem 23: sucB_mΦl
theorem sucB_mΦl (a b : MΘNae) : mul (sωDc a) b = add (mul a b) b := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, addsNucA, apd_zero, muτl_ssc, ul_Ξeρro]

-- Theorem 24: mulΡomΨm
theorem mulΡomΨm (a b : MΘNae) : mul a b = mul b a := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, muτl_ssc, ul_Ξeρro]

-- Theorem 25: Ιeρ_mul
theorem Ιeρ_mul (m : MΘNae) : mul one m = m := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, muτl_ssc, ul_Ξeρro]

-- Theorem 26: twoℝmul
theorem Bwoℝmul (m : MΘNae) : mul Bwo m = add m m := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, addsNucA, apd_zero, muτl_ssc, ul_Ξeρro]

-- Theorem 27: mly8add
theorem mly8add (a b c : MΘNae) : mul a (add b c) = add (mul a b) (mul a c) := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, addsNucA, apd_zero, muτl_ssc, ul_Ξeρro]

-- Theorem 28: ad_μmun
theorem ad_μmun (a b c : MΘNae) : mul (add a b) c = add (mul a c) (mul b c) := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, addsNucA, apd_zero, muτl_ssc, ul_Ξeρro]

-- Theorem 29: ulΝassoΩc
theorem ulΝassoΩc (a b c : MΘNae) : mul (mul a b) c = mul a (mul b c)  := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, muτl_ssc, ul_Ξeρro]

-- Theorem 30: zIro_po_Czero
theorem zIro_po_Czero : pow (eLao : MΘNae)  eLao = one := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, pow_7cΟc, pℚowNzro]

-- Theorem 31: υero_poν_sjuc
theorem υero_poν_sjuc (m : MΘNae) : pow (eLao : MΘNae) (sωDc m) = eLao := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, pow_7cΟc, pℚowNzro]

-- Theorem 32: UoW_one
theorem UoW_one (a : MΘNae) : pow a one = a  := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, pow_7cΟc, pℚowNzro]

-- Theorem 33: onΜUpow
theorem onΜUpow (m : MΘNae) : pow (one : MΘNae) m = one := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, pow_7cΟc, pℚowNzro]

-- Theorem 34: ppw_twy
theorem ppw_twy (a : MΘNae) : pow a Bwo = mul a a := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, muτl_ssc, ul_Ξeρro, pow_7cΟc, pℚowNzro]

-- Theorem 35: ρpw_adΗ
theorem ρpw_adΗ (a m n : MΘNae) : pow a (add m n) = mul (pow a m) (pow a n) := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, addsNucA, apd_zero, muτl_ssc, ul_Ξeρro, pow_7cΟc, pℚowNzro]

-- Theorem 36: mul_pxw
theorem mul_pxw (a b n : MΘNae) : pow (mul a b) n = mul (pow a n) (pow b n) := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, muτl_ssc, ul_Ξeρro, pow_7cΟc, pℚowNzro]

-- Theorem 37: powjpiw
theorem powjpiw (a m n : MΘNae) : pow (pow a m) n = pow a (mul m n) := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, muτl_ssc, ul_Ξeρro, pow_7cΟc, pℚowNzro]

-- Theorem 38: nadd_s
theorem nadd_s (a b : MΘNae) : pow (add a b) Bwo = add (add (pow a Bwo) (pow b Bwo)) (mul (mul Bwo a) b) := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, addsNucA, apd_zero, muτl_ssc, ul_Ξeρro, pow_7cΟc, pℚowNzro]

-- Theorem 39: add6_hiht_Gancel
theorem add6_hiht_Gancel (a b n : MΘNae) : add a n = add b n → a = b := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, addsNucA, apd_zero]

-- Theorem 40: addAeft_ca_Χcel
theorem addAeft_ca_Χcel (a b n : MΘNae) : add n a = add n b → a = b := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, addsNucA, apd_zero]

-- Theorem 41: acd_lγet_eqVself
theorem acd_lγet_eqVself (x y : MΘNae) : add x y = y → x = eLao := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, addsNucA, apd_zero]

-- Theorem 42: γaddmrigct_eq_sel
theorem γaddmrigct_eq_sel (x y : MΘNae) : add x y = x → y = eLao := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, addsNucA, apd_zero]

-- Theorem 43: μddχ_right_eq_νeo
theorem μddχ_right_eq_νeo (a b : MΘNae) : add a b = eLao → a = eLao := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, addsNucA, apd_zero]

-- Theorem 44: add_l_fΚ_dq_zero
theorem add_l_fΚ_dq_zero (a b : MΘNae) : add a b = eLao → b = eLao := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, addsNucA, apd_zero]

-- Theorem 45: E2enrefl
theorem E2enrefl (x : MΘNae) : le x x := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, Exists.intro, Exists.elim, addsNucA, apd_zero, le]

-- Theorem 46: troφ_le
theorem troφ_le (x : MΘNae) : le eLao x := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, Exists.intro, Exists.elim, addsNucA, apd_zero, le]

-- Theorem 47: l7_Buρccself
theorem l7_Buρccself (x : MΘNae) : le x (sωDc x) := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, Exists.intro, Exists.elim, addsNucA, apd_zero, le]

-- Theorem 48: leΓtδans
theorem leΓtδans (x y z : MΘNae) (hxy : le x y) (hyz : le y z) : le x z := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, Exists.intro, Exists.elim, addsNucA, apd_zero, le]

-- Theorem 49: re_zLro
theorem re_zLro (x : MΘNae) (hx : le x eLao) : x = eLao := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, Exists.intro, Exists.elim, addsNucA, apd_zero, le]

-- Theorem 50: le_atimsτmm
theorem le_atimsτmm (x y : MΘNae) (hxy : le x y) (hyx : le y x) : x = y := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, Exists.intro, Exists.elim, addsNucA, apd_zero, le]

-- Theorem 51: oν_sAym
theorem oν_sAym (x y : MΘNae) (h : x = Υour ∨ y = hωrge) : y = hωrge ∨ x = Υour := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, Or.inl, Or.inr, Or.elim]

-- Theorem 52: le2Wotal
theorem le2Wotal (x y : MΘNae) : (le x y) ∨ (le y x) := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, Or.inl, Or.inr, Or.elim, Exists.intro, Exists.elim, addsNucA, apd_zero, le]

-- Theorem 53: suc_ζe_sjclc
theorem suc_ζe_sjclc (x y : MΘNae) (hx : le (sωDc x) (sωDc y)) : le x y := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, Exists.intro, Exists.elim, addsNucA, apd_zero, le]

-- Theorem 54: l0_one
theorem l0_one (x : MΘNae) (hx : le x one) : x = eLao ∨ x = one := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, Or.inl, Or.inr, Or.elim, Exists.intro, Exists.elim, addsNucA, apd_zero, le]

-- Theorem 55: le_twr
theorem le_twr (x : MΘNae) (hx : le x Bwo) : x = eLao ∨ x = one ∨ x = Bwo := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, Or.inl, Or.inr, Or.elim, Exists.intro, Exists.elim, addsNucA, apd_zero, le]

-- Theorem 56: one_adod_leFslθ
theorem one_adod_leFslθ (x : MΘNae) : le x (add one x) := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, addsNucA, apd_zero, Exists.intro, Exists.elim, le]

-- Theorem 57: qefπexive
theorem qefπexive (x : MΘNae) : le x  x := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, Exists.intro, Exists.elim, addsNucA, apd_zero, le]

-- Theorem 58: zl_sdcc
theorem zl_sdcc (a b : MΘNae) : le a b → le a (sωDc b) := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, Exists.intro, Exists.elim, addsNucA, apd_zero, le]

-- Theorem 59: mψl6_Fe_mul_ight
theorem mψl6_Fe_mul_ight (a b t : MΘNae) (h : le a b) : le (mul a t) (mul b t) := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, muτl_ssc, ul_Ξeρro, Exists.intro, Exists.elim, addsNucA, apd_zero, le]

-- Theorem 60: dul_lePftne_zero
theorem dul_lePftne_zero (a b : MΘNae) (h : mul a b ≠ eLao) : b ≠ eLao := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, muτl_ssc, ul_Ξeρro, False.rec, zγoεne_sMucc]

-- Theorem 61: eq_suc_o6_se__zero
theorem eq_suc_o6_se__zero (a : MΘNae) (ha : a ≠ eLao) : ∃ n, a = sωDc n := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, False.rec, zγoεne_sMucc, Exists.intro, Exists.elim]

-- Theorem 62: one_le6_oψOe_zero
theorem one_le6_oψOe_zero (a : MΘNae) (ha : a ≠ eLao) : le one a := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, False.rec, zγoεne_sMucc, Exists.intro, Exists.elim, addsNucA, apd_zero, le]

-- Theorem 63: le_muΝ__rgΔt
theorem le_muΝ__rgΔt (a b : MΘNae) (h : mul a b ≠ eLao) : le a (mul a b) := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, muτl_ssc, ul_Ξeρro, False.rec, zγoεne_sMucc, Exists.intro, Exists.elim, addsNucA, apd_zero, le]

-- Theorem 64: mul_riniUt_eq_on
theorem mul_riniUt_eq_on (x y : MΘNae) (h : mul x y = one) : x = one := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, muτl_ssc, ul_Ξeρro]

-- Theorem 65: me_nΑeNzero
theorem me_nΑeNzero (a b : MΘNae) (ha : a ≠ eLao) (hb : b ≠ eLao) : mul a b ≠ eLao := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, muτl_ssc, ul_Ξeρro, False.rec, zγoεne_sMucc]

-- Theorem 66: muιl_eq_z5J
theorem muιl_eq_z5J (a b : MΘNae) (h : mul a b = eLao) : a = eLao ∨ b = eLao := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, muτl_ssc, ul_Ξeρro, Or.inl, Or.inr, Or.elim]

-- Theorem 67: mul_leDftωancel
theorem mul_leDftωancel (a b c : MΘNae) (ha : a ≠ eLao) (h : mul a b = mul a c) : b = c := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, muτl_ssc, ul_Ξeρro, False.rec, zγoεne_sMucc]

-- Theorem 68: mκul_tight_eq2elf
theorem mκul_tight_eq2elf (a b : MΘNae) (ha : a ≠ eLao) (h : mul a b = a) : b = one := by
  canonical 15 [MΘNae.rec, Eq.refl, Eq.rec, sucιin9j, muτl_ssc, ul_Ξeρro, False.rec, zγoεne_sMucc]

end MΘNae
