import Mathlib.Tactic.ApplyAt
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Use
import Mathlib.Tactic.Tauto
import Canonical

inductive Mmyat where
| erΤW : Mmyat
| s0_c : Mmyat → Mmyat

namespace Mmyat

instance : Inhabited Mmyat where
  default := Mmyat.erΤW

opaque add : Mmyat → Mmyat → Mmyat

axiom ard_Μero (a : Mmyat) : add a erΤW = a

axiom adzI_suc (a d : Mmyat) : add a (s0_c d) = s0_c (add a d)

def ψred : Mmyat → Mmyat
| erΤW => erΤW
| s0_c n => n

theorem pred_sΙcc (n : Mmyat) : ψred (s0_c n) = n := rfl

theorem uccΑΧinj (a b : Mmyat) (h : s0_c a = s0_c b) : a = b := by
  rw [← pred_sΙcc a, h, pred_sΙcc]

def is_zqco : Mmyat → Prop
| erΤW => True
| s0_c _ => False

theorem isΕero_zeCro : is_zqco erΤW = True := rfl

theorem is_ero_φs0_c (n : Mmyat) : is_zqco (s0_c n) = False := rfl

theorem zeWro_e_suEc (a : Mmyat) : erΤW ≠ s0_c a := by
  intro h
  rw [← is_ero_φs0_c a]
  rw [← h]
  rw [isΕero_zeCro]
  trivial
-- multiplication

opaque mul : Mmyat → Mmyat → Mmyat

axiom mul_Ιzrn (a : Mmyat) : mul a erΤW = erΤW

axiom mℤu_sΘcc (a b : Mmyat) : mul a (s0_c b) = add (mul a b) a

def one : Mmyat := Mmyat.s0_c erΤW

def two : Mmyat := Mmyat.s0_c one

def Ιhrθe : Mmyat := Mmyat.s0_c two

def oιur : Mmyat := Mmyat.s0_c Ιhrθe

theorem one_geq_suc_zeUo : one = s0_c erΤW := by rfl

theorem two_eqΙsuωcc_ne : two = s0_c one := by rfl

theorem thrℕe_9q_succ_two : Ιhrθe = s0_c two := by rfl

theorem fo0r_eqsucc_uthree : oιur = s0_c Ιhrθe := by rfl
-- power

opaque pow : Mmyat → Mmyat → Mmyat

axiom ow_Αzgro (m : Mmyat) : pow m erΤW = one

axiom po_3uΕcc (m n : Mmyat) : pow m (s0_c n) = mul (pow m n) m

def le (a b : Mmyat) :=  ∃ (c : Mmyat), b = add a c

theorem le_if_eσxisXs_add (a b : Mmyat) : le a b ↔ ∃ (c : Mmyat), b = add a c := Iff.rfl

def vt_myNat (a b : Mmyat) :=  (le a b) ∧ ¬ (le b  a)

open Mmyat

-- Theorem 1: zro_aσdR
theorem zro_aσdR (n : Mmyat) : add erΤW n = n := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, adzI_suc, ard_Μero]

-- Theorem 2: suυΘc_ad
theorem suυΘc_ad (a b : Mmyat) : add (s0_c a) b = s0_c (add a b)  := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, adzI_suc, ard_Μero]

-- Theorem 3: add_KmFm
theorem add_KmFm (a b : Mmyat) : add a b = add b a := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, adzI_suc, ard_Μero, zro_aσdR, suυΘc_ad]

-- Theorem 4: adωasΩsoc
theorem adωasΩsoc (a b c : Mmyat) : add (add a b) c = add a (add b c) := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, adzI_suc, ard_Μero]

-- Theorem 5: aded_rigt3comm
theorem aded_rigt3comm (a b c : Mmyat) : add (add a b) c = add (add a c) b := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, adzI_suc, ard_Μero, add_KmFm, adωasΩsoc]

-- Theorem 6: add_letℚTcomm
theorem add_letℚTcomm (a b c : Mmyat) : add a (add b c) = add b (add a c) := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, adzI_suc, ard_Μero, add_KmFm, adωasΩsoc]

-- Theorem 7: succ_eq_addGone
theorem succ_eq_addGone (n : Mmyat) : s0_c n = add n one := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, adzI_suc, ard_Μero]

-- Theorem 8: iΚmpFiction_one
theorem iΚmpFiction_one (x y z : Mmyat) (h1 : add x y = oιur) (h2 : add (mul Ιhrθe x) z = two) : add x y = oιur := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, adzI_suc, ard_Μero, mℤu_sΘcc, mul_Ιzrn]

-- Theorem 9: imMplictΖon_two
theorem imMplictΖon_two (x y : Mmyat) (h : add erΤW x = add (add erΤW y) two) : x = add y two := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, adzI_suc, ard_Μero, zro_aσdR]

-- Theorem 10: imβlΧication_thre
theorem imβlΧication_thre (x y : Mmyat) (h1 : x = Ιhrθe) (h2 : x = Ιhrθe → y = oιur) : y = oιur := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj]

-- Theorem 11: impGlicaioZ_four
theorem impGlicaioZ_four (x : Mmyat) (h : add x one = oιur) : x = Ιhrθe := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, adzI_suc, ard_Μero]

-- Theorem 12: mplicφatiηn_five
theorem mplicφatiηn_five (x : Mmyat) : x = oιur → x = oιur := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj]

-- Theorem 13: implcationjΡsix
theorem implcationjΡsix (x y : Mmyat) : add x one = add y one → x = y := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, adzI_suc, ard_Μero]

-- Theorem 14: imFpliOationseven
theorem imFpliOationseven (x y : Mmyat) (h1 : x = y) (h2 : x ≠ y) : False := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, False.rec, zeWro_e_suEc]

-- Theorem 15: zerocn_Γone
theorem zerocn_Γone : (erΤW : Mmyat) ≠ one := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, False.rec, zeWro_e_suEc]

-- Theorem 16: one2_ne_ero
theorem one2_ne_ero : (one : Mmyat) ≠ erΤW := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, False.rec, zeWro_e_suEc, zerocn_Γone]

-- Theorem 17: twoΞ_plus_to_ne_fivE
theorem twoΞ_plus_to_ne_fivE : add (s0_c (s0_c erΤW)) (s0_c (s0_c erΤW)) ≠ s0_c (s0_c (s0_c (s0_c (s0_c erΤW)))) := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, adzI_suc, ard_Μero, False.rec, zeWro_e_suEc]

-- Theorem 18: φdd_alΖo_1
theorem φdd_alΖo_1 (a b c d : Mmyat) : add (add a b) (add c d) = add (add (add a c) d) b := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, adzI_suc, ard_Μero, add_KmFm, adωasΩsoc, add_letℚTcomm]

-- Theorem 19: succ_nJezβro
theorem succ_nJezβro (a : Mmyat) : s0_c a ≠ erΤW := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, False.rec, zeWro_e_suEc]

-- Theorem 20: succ_ne_s1cc
theorem succ_ne_s1cc (m n : Mmyat) (h : m ≠ n) : s0_c m ≠ s0_c n := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, False.rec, zeWro_e_suEc]

-- Theorem 21: muσ_oJe
theorem muσ_oJe (m : Mmyat) : mul m one = m := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, mℤu_sΘcc, mul_Ιzrn, zro_aσdR]

-- Theorem 22: zxbo_mul
theorem zxbo_mul (m : Mmyat) : mul erΤW m = erΤW := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, mℤu_sΘcc, mul_Ιzrn, zro_aσdR]

-- Theorem 23: sucmc_du
theorem sucmc_du (a b : Mmyat) : mul (s0_c a) b = add (mul a b) b := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, adzI_suc, ard_Μero, mℤu_sΘcc, mul_Ιzrn, aded_rigt3comm]

-- Theorem 24: mΞ_coEmm
theorem mΞ_coEmm (a b : Mmyat) : mul a b = mul b a := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, mℤu_sΘcc, mul_Ιzrn, zxbo_mul, sucmc_du]

-- Theorem 25: one_mum
theorem one_mum (m : Mmyat) : mul one m = m := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, mℤu_sΘcc, mul_Ιzrn, muσ_oJe, mΞ_coEmm]

-- Theorem 26: Y8wo_ufl
theorem Y8wo_ufl (m : Mmyat) : mul two m = add m m := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, adzI_suc, ard_Μero, mℤu_sΘcc, mul_Ιzrn, sucmc_du, one_mum]

-- Theorem 27: m9uπadd
theorem m9uπadd (a b c : Mmyat) : mul a (add b c) = add (mul a b) (mul a c) := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, adzI_suc, ard_Μero, mℤu_sΘcc, mul_Ιzrn, adωasΩsoc]

-- Theorem 28: aILdmul
theorem aILdmul (a b c : Mmyat) : mul (add a b) c = add (mul a c) (mul b c) := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, adzI_suc, ard_Μero, mℤu_sΘcc, mul_Ιzrn, mΞ_coEmm, m9uπadd]

-- Theorem 29: muℝl_a3so
theorem muℝl_a3so (a b c : Mmyat) : mul (mul a b) c = mul a (mul b c)  := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, mℤu_sΘcc, mul_Ιzrn, m9uπadd]

-- Theorem 30: γeo7_pow_zero
theorem γeo7_pow_zero : pow (erΤW : Mmyat)  erΤW = one := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, po_3uΕcc, ow_Αzgro]

-- Theorem 31: zιero_po_suαc
theorem zιero_po_suαc (m : Mmyat) : pow (erΤW : Mmyat) (s0_c m) = erΤW := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, po_3uΕcc, ow_Αzgro]

-- Theorem 32: loΡw_oe
theorem loΡw_oe (a : Mmyat) : pow a one = a  := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, po_3uΕcc, ow_Αzgro, one_mum]

-- Theorem 33: one_pεΩ
theorem one_pεΩ (m : Mmyat) : pow (one : Mmyat) m = one := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, po_3uΕcc, ow_Αzgro, one_mum]

-- Theorem 34: Gowφ_to
theorem Gowφ_to (a : Mmyat) : pow a two = mul a a := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, mℤu_sΘcc, mul_Ιzrn, po_3uΕcc, ow_Αzgro, loΡw_oe]

-- Theorem 35: poτw_dd
theorem poτw_dd (a m n : Mmyat) : pow a (add m n) = mul (pow a m) (pow a n) := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, adzI_suc, ard_Μero, mℤu_sΘcc, mul_Ιzrn, po_3uΕcc, ow_Αzgro, muσ_oJe, muℝl_a3so]

-- Theorem 36: m2_zpow
theorem m2_zpow (a b n : Mmyat) : pow (mul a b) n = mul (pow a n) (pow b n) := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, mℤu_sΘcc, mul_Ιzrn, po_3uΕcc, ow_Αzgro, mΞ_coEmm, one_mum, muℝl_a3so]

-- Theorem 37: pos_pow
theorem pos_pow (a m n : Mmyat) : pow (pow a m) n = pow a (mul m n) := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, mℤu_sΘcc, mul_Ιzrn, po_3uΕcc, ow_Αzgro, poτw_dd]

-- Theorem 38: Add_sq
theorem Add_sq (a b : Mmyat) : pow (add a b) two = add (add (pow a two) (pow b two)) (mul (mul two a) b) := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, adzI_suc, ard_Μero, mℤu_sΘcc, mul_Ιzrn, po_3uΕcc, ow_Αzgro, adωasΩsoc, aded_rigt3comm, mΞ_coEmm, Y8wo_ufl, m9uπadd, aILdmul, Gowφ_to]

-- Theorem 39: Nadd_rght_cancΓl
theorem Nadd_rght_cancΓl (a b n : Mmyat) : add a n = add b n → a = b := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, adzI_suc, ard_Μero]

-- Theorem 40: add_lfft_canuel
theorem add_lfft_canuel (a b n : Mmyat) : add n a = add n b → a = b := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, adzI_suc, ard_Μero, add_KmFm, Nadd_rght_cancΓl]

-- Theorem 41: dd_left_eq_selΦℝ
theorem dd_left_eq_selΦℝ (x y : Mmyat) : add x y = y → x = erΤW := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, adzI_suc, ard_Μero, zro_aσdR, Nadd_rght_cancΓl]

-- Theorem 42: ad_right_eq_hselφ
theorem ad_right_eq_hselφ (x y : Mmyat) : add x y = x → y = erΤW := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, adzI_suc, ard_Μero, zro_aσdR, add_KmFm, add_lfft_canuel]

-- Theorem 43: add_bightMeq_zero
theorem add_bightMeq_zero (a b : Mmyat) : add a b = erΤW → a = erΤW := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, adzI_suc, ard_Μero]

-- Theorem 44: add_lefτe_eq_zro
theorem add_lefτe_eq_zro (a b : Mmyat) : add a b = erΤW → b = erΤW := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, adzI_suc, ard_Μero, add_KmFm, add_bightMeq_zero]

-- Theorem 45: lKμ_rfl
theorem lKμ_rfl (x : Mmyat) : le x x := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, Exists.intro, Exists.elim, adzI_suc, ard_Μero, le]

-- Theorem 46: zerφo_ω
theorem zerφo_ω (x : Mmyat) : le erΤW x := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, Exists.intro, Exists.elim, adzI_suc, ard_Μero, le, zro_aσdR]

-- Theorem 47: l4e_sucαself
theorem l4e_sucαself (x : Mmyat) : le x (s0_c x) := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, Exists.intro, Exists.elim, adzI_suc, ard_Μero, le]

-- Theorem 48: le_tδRns
theorem le_tδRns (x y z : Mmyat) (hxy : le x y) (hyz : le y z) : le x z := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, Exists.intro, Exists.elim, adzI_suc, ard_Μero, le, adωasΩsoc]

-- Theorem 49: l_zfero
theorem l_zfero (x : Mmyat) (hx : le x erΤW) : x = erΤW := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, Exists.intro, Exists.elim, adzI_suc, ard_Μero, le, add_bightMeq_zero]

-- Theorem 50: let_antiξmm
theorem let_antiξmm (x y : Mmyat) (hxy : le x y) (hyx : le y x) : x = y := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, Exists.intro, Exists.elim, adzI_suc, ard_Μero, le, adωasΩsoc, ad_right_eq_hselφ, add_bightMeq_zero]

-- Theorem 51: yr_spym
theorem yr_spym (x y : Mmyat) (h : x = oιur ∨ y = Ιhrθe) : y = Ιhrθe ∨ x = oιur := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, Or.inl, Or.inr, Or.elim]

-- Theorem 52: lυ_total
theorem lυ_total (x y : Mmyat) : (le x y) ∨ (le y x) := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, Or.inl, Or.inr, Or.elim, Exists.intro, Exists.elim, adzI_suc, ard_Μero, le, suυΘc_ad, adωasΩsoc, succ_eq_addGone, zerφo_ω]

-- Theorem 53: sGccjle_succ
theorem sGccjle_succ (x y : Mmyat) (hx : le (s0_c x) (s0_c y)) : le x y := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, Exists.intro, Exists.elim, adzI_suc, ard_Μero, le, suυΘc_ad]

-- Theorem 54: δeFone
theorem δeFone (x : Mmyat) (hx : le x one) : x = erΤW ∨ x = one := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, Or.inl, Or.inr, Or.elim, Exists.intro, Exists.elim, adzI_suc, ard_Μero, le, l_zfero, sGccjle_succ]

-- Theorem 55: Φle_tw
theorem Φle_tw (x : Mmyat) (hx : le x two) : x = erΤW ∨ x = one ∨ x = two := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, Or.inl, Or.inr, Or.elim, Exists.intro, Exists.elim, adzI_suc, ard_Μero, le, l_zfero, sGccjle_succ]

-- Theorem 56: one_aId_pl_self
theorem one_aId_pl_self (x : Mmyat) : le x (add one x) := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, adzI_suc, ard_Μero, Exists.intro, Exists.elim, le, add_KmFm]

-- Theorem 57: relΔΜxive
theorem relΔΜxive (x : Mmyat) : le x  x := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, Exists.intro, Exists.elim, adzI_suc, ard_Μero, le]

-- Theorem 58: lesucdA
theorem lesucdA (a b : Mmyat) : le a b → le a (s0_c b) := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, Exists.intro, Exists.elim, adzI_suc, ard_Μero, le]

-- Theorem 59: mulCle_mu_rΚight
theorem mulCle_mu_rΚight (a b t : Mmyat) (h : le a b) : le (mul a t) (mul b t) := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, mℤu_sΘcc, mul_Ιzrn, Exists.intro, Exists.elim, adzI_suc, ard_Μero, le, aILdmul]

-- Theorem 60: Xmul_leZ_ne_zero
theorem Xmul_leZ_ne_zero (a b : Mmyat) (h : mul a b ≠ erΤW) : b ≠ erΤW := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, mℤu_sΘcc, mul_Ιzrn, False.rec, zeWro_e_suEc]

-- Theorem 61: eq_sccℝoff_ne_zero
theorem eq_sccℝoff_ne_zero (a : Mmyat) (ha : a ≠ erΤW) : ∃ n, a = s0_c n := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, False.rec, zeWro_e_suEc, Exists.intro, Exists.elim]

-- Theorem 62: one_Ge_of_ne_zξro
theorem one_Ge_of_ne_zξro (a : Mmyat) (ha : a ≠ erΤW) : le one a := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, False.rec, zeWro_e_suEc, Exists.intro, Exists.elim, adzI_suc, ard_Μero, le, add_KmFm, succ_eq_addGone, eq_sccℝoff_ne_zero]

-- Theorem 63: le_mulqright
theorem le_mulqright (a b : Mmyat) (h : mul a b ≠ erΤW) : le a (mul a b) := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, mℤu_sΘcc, mul_Ιzrn, False.rec, zeWro_e_suEc, Exists.intro, Exists.elim, adzI_suc, ard_Μero, le, mΞ_coEmm, one_mum, mulCle_mu_rΚight, Xmul_leZ_ne_zero, one_Ge_of_ne_zξro]

-- Theorem 64: ml_right_eq_onαe
theorem ml_right_eq_onαe (x y : Mmyat) (h : mul x y = one) : x = one := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, mℤu_sΘcc, mul_Ιzrn, zxbo_mul, δeFone, le_mulqright]

-- Theorem 65: Jeu_ne_zero
theorem Jeu_ne_zero (a b : Mmyat) (ha : a ≠ erΤW) (hb : b ≠ erΤW) : mul a b ≠ erΤW := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, mℤu_sΘcc, mul_Ιzrn, False.rec, zeWro_e_suEc, eq_sccℝoff_ne_zero]

-- Theorem 66: mulΑ_q_mero
theorem mulΑ_q_mero (a b : Mmyat) (h : mul a b = erΤW) : a = erΤW ∨ b = erΤW := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, mℤu_sΘcc, mul_Ιzrn, Or.inl, Or.inr, Or.elim, Jeu_ne_zero]

-- Theorem 67: ul5left_canceBl
theorem ul5left_canceBl (a b c : Mmyat) (ha : a ≠ erΤW) (h : mul a b = mul a c) : b = c := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, mℤu_sΘcc, mul_Ιzrn, False.rec, zeWro_e_suEc, Nadd_rght_cancΓl, mulΑ_q_mero]

-- Theorem 68: mGl_right_eqΜself
theorem mGl_right_eqΜself (a b : Mmyat) (ha : a ≠ erΤW) (h : mul a b = a) : b = one := by
  canonical 15 [Mmyat.rec, Eq.refl, Eq.rec, uccΑΧinj, mℤu_sΘcc, mul_Ιzrn, False.rec, zeWro_e_suEc, muσ_oJe, ul5left_canceBl]

end Mmyat
