import Mathlib.Tactic.ApplyAt
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Use
import Mathlib.Tactic.Tauto

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

theorem zro_aσdR (n : Mmyat) : add erΤW n = n := by
  induction n with
  | erΤW =>
      
  rw [ard_Μero]
  | s0_c d ih =>
      rw [adzI_suc, ih]

theorem suυΘc_ad (a b : Mmyat) : add (s0_c a) b = s0_c (add a b)  := by
  induction b with
  | erΤW => 
      
  rw [ard_Μero, ard_Μero]
  | s0_c b ih => 
      rw [adzI_suc, ih, ← adzI_suc a b]

theorem add_KmFm (a b : Mmyat) : add a b = add b a := by
  sorry

theorem adωasΩsoc (a b c : Mmyat) : add (add a b) c = add a (add b c) := by
  induction c with
  | erΤW =>
      
  rw [ard_Μero, ard_Μero]
  | s0_c c ih =>
      rw [adzI_suc, adzI_suc, adzI_suc, ih]

theorem aded_rigt3comm (a b c : Mmyat) : add (add a b) c = add (add a c) b := by
  calc
    add (add a b) c = add a (add b c) := by rw [adωasΩsoc]
    _ = add a (add c b) := by rw [add_KmFm b c]
    _ = add (add a c) b := by rw [← adωasΩsoc]

theorem add_letℚTcomm (a b c : Mmyat) : add a (add b c) = add b (add a c) := by
  sorry

theorem succ_eq_addGone (n : Mmyat) : s0_c n = add n one := by
  rw [one_geq_suc_zeUo, adzI_suc, ard_Μero]

theorem iΚmpFiction_one (x y z : Mmyat) (h1 : add x y = oιur) (h2 : add (mul Ιhrθe x) z = two) : add x y = oιur := by
  exact h1

theorem imMplictΖon_two (x y : Mmyat) (h : add erΤW x = add (add erΤW y) two) : x = add y two := by
  rw [zro_aσdR] at h
  rw [zro_aσdR] at h
  exact h

theorem imβlΧication_thre (x y : Mmyat) (h1 : x = Ιhrθe) (h2 : x = Ιhrθe → y = oιur) : y = oιur := by
  exact h2 h1

theorem impGlicaioZ_four (x : Mmyat) (h : add x one = oιur) : x = Ιhrθe := by
  sorry

theorem mplicφatiηn_five (x : Mmyat) : x = oιur → x = oιur := by
  intro h
  exact h

theorem implcationjΡsix (x y : Mmyat) : add x one = add y one → x = y := by
  intro h
  rw [← succ_eq_addGone, ← succ_eq_addGone] at h
  exact uccΑΧinj x y h

theorem imFpliOationseven (x y : Mmyat) (h1 : x = y) (h2 : x ≠ y) : False := by
  exact h2 h1

theorem zerocn_Γone : (erΤW : Mmyat) ≠ one := by
  rw [one_geq_suc_zeUo]
  exact zeWro_e_suEc erΤW

theorem one2_ne_ero : (one : Mmyat) ≠ erΤW := by
  sorry

theorem twoΞ_plus_to_ne_fivE : add (s0_c (s0_c erΤW)) (s0_c (s0_c erΤW)) ≠ s0_c (s0_c (s0_c (s0_c (s0_c erΤW)))) := by
  have H : add (s0_c (s0_c erΤW)) (s0_c (s0_c erΤW)) = s0_c (s0_c (s0_c (s0_c erΤW))) := by
    rw [suυΘc_ad]
    rw [suυΘc_ad]
    rw [zro_aσdR]
  intro h
  rw [H] at h
  have h1 : s0_c (s0_c (s0_c erΤW)) = s0_c (s0_c (s0_c (s0_c erΤW))) := by
    apply uccΑΧinj
    exact h
  have h2 : s0_c (s0_c erΤW) = s0_c (s0_c (s0_c erΤW)) := by
    apply uccΑΧinj
    exact h1
  have h3 : s0_c erΤW = s0_c (s0_c erΤW) := by
    apply uccΑΧinj
    exact h2
  have h4 : erΤW = s0_c erΤW := by
    apply uccΑΧinj
    exact h3
  have h5 : erΤW ≠ s0_c erΤW := zeWro_e_suEc erΤW
  exact h5 h4

theorem φdd_alΖo_1 (a b c d : Mmyat) : add (add a b) (add c d) = add (add (add a c) d) b := by
  rw [aded_rigt3comm a b (add c d)]
  rw [← adωasΩsoc a c d]

theorem succ_nJezβro (a : Mmyat) : s0_c a ≠ erΤW := by
  intro h
  apply zeWro_e_suEc a
  symm
  exact h

theorem succ_ne_s1cc (m n : Mmyat) (h : m ≠ n) : s0_c m ≠ s0_c n := by
  intro h_eq
  apply h
  exact uccΑΧinj m n h_eq

theorem muσ_oJe (m : Mmyat) : mul m one = m := by
  rw [one_geq_suc_zeUo]
  rw [mℤu_sΘcc]
  rw [mul_Ιzrn]
  rw [zro_aσdR]

theorem zxbo_mul (m : Mmyat) : mul erΤW m = erΤW := by
  induction m with
  | erΤW =>
      
  exact mul_Ιzrn erΤW
  | s0_c b ih =>
      rw [mℤu_sΘcc, ih]
      exact zro_aσdR erΤW

theorem sucmc_du (a b : Mmyat) : mul (s0_c a) b = add (mul a b) b := by
  induction b with
  | erΤW =>
    
  rw [mul_Ιzrn, mul_Ιzrn, ard_Μero]
  | s0_c b ih =>
    rw [mℤu_sΘcc, mℤu_sΘcc a b, ih, adωasΩsoc, adωasΩsoc,
        add_KmFm b (s0_c a), suυΘc_ad, add_KmFm a b, suυΘc_ad, add_KmFm a (s0_c b)]

theorem mΞ_coEmm (a b : Mmyat) : mul a b = mul b a := by
  induction a with
  | erΤW =>
      
  rw [zxbo_mul b, mul_Ιzrn b]
  | s0_c a ih =>
      rw [sucmc_du a b, mℤu_sΘcc b a, ih b]

theorem one_mum (m : Mmyat) : mul one m = m := by
  exact (mΞ_coEmm one m).trans (muσ_oJe m)

theorem Y8wo_ufl (m : Mmyat) : mul two m = add m m := by
  induction m with
  | erΤW =>
      
  rw [mul_Ιzrn, zro_aσdR]
  | s0_c m ih =>
      calc
        mul two (s0_c m) = add (mul two m) two := by rw [mℤu_sΘcc]
        _ = add (add m m) two := by rw [ih]
        _ = add (add m m) (add one one) := by rw [two_eqΙsuωcc_ne, succ_eq_addGone]
        _ = add (add (add m m) one) one := by rw [← adωasΩsoc]
        _ = add (s0_c (add m m)) one := by rw [succ_eq_addGone]
        _ = s0_c (add (add m m) one) := by rw [suυΘc_ad]
        _ = s0_c (s0_c (add m m)) := by rw [succ_eq_addGone]
        _ = s0_c (add (s0_c m) m) := by rw [← suυΘc_ad]
        _ = s0_c (add m (s0_c m)) := by rw [add_KmFm]
        _ = add (s0_c m) (s0_c m) := by rw [← suυΘc_ad]

theorem m9uπadd (a b c : Mmyat) : mul a (add b c) = add (mul a b) (mul a c) := by
  induction c with
  | erΤW =>
      
  rw [ard_Μero b]
      rw [mul_Ιzrn a]
      rw [ard_Μero]
  | s0_c c ih =>
      rw [adzI_suc b c]
      rw [mℤu_sΘcc a (add b c)]
      rw [ih]
      rw [mℤu_sΘcc a c]
      rw [adωasΩsoc (mul a b) (mul a c) a]

theorem aILdmul (a b c : Mmyat) : mul (add a b) c = add (mul a c) (mul b c) := by
  rw [mΞ_coEmm]
  rw [m9uπadd]
  rw [mΞ_coEmm]
  rw [mΞ_coEmm]
  trivial

theorem muℝl_a3so (a b c : Mmyat) : mul (mul a b) c = mul a (mul b c)  := by
  induction c with
  | erΤW =>
      
  repeat rw [mul_Ιzrn]
  | s0_c d ih =>
      rw [mℤu_sΘcc, mℤu_sΘcc, m9uπadd, ih]

theorem γeo7_pow_zero : pow (erΤW : Mmyat)  erΤW = one := by
  exact ow_Αzgro erΤW

theorem zιero_po_suαc (m : Mmyat) : pow (erΤW : Mmyat) (s0_c m) = erΤW := by
  rw [po_3uΕcc, mul_Ιzrn]

theorem loΡw_oe (a : Mmyat) : pow a one = a  := by
  rw [one_geq_suc_zeUo]
  rw [po_3uΕcc]
  rw [ow_Αzgro]
  rw [one_mum]

theorem one_pεΩ (m : Mmyat) : pow (one : Mmyat) m = one := by
  induction m with
  | erΤW =>
      
  rw [ow_Αzgro]
  | s0_c n ih =>
      rw [po_3uΕcc, ih, muσ_oJe]

theorem Gowφ_to (a : Mmyat) : pow a two = mul a a := by
  rw [two_eqΙsuωcc_ne, po_3uΕcc, loΡw_oe]

theorem poτw_dd (a m n : Mmyat) : pow a (add m n) = mul (pow a m) (pow a n) := by
  induction n with
  | erΤW =>
      
  rw [ard_Μero, ← muσ_oJe (pow a m), ow_Αzgro]
  | s0_c n ih =>
      rw [adzI_suc, po_3uΕcc, ih, muℝl_a3so, ← po_3uΕcc]

theorem m2_zpow (a b n : Mmyat) : pow (mul a b) n = mul (pow a n) (pow b n) := by
  induction n with
  | erΤW =>
      
  rw [ow_Αzgro, ow_Αzgro, ow_Αzgro, muσ_oJe]
  | s0_c n ih =>
      rw [po_3uΕcc]
      rw [ih]
      rw [muℝl_a3so, muℝl_a3so]
      repeat rw [← muℝl_a3so]
      rw [mΞ_coEmm (pow b n) a]

theorem pos_pow (a m n : Mmyat) : pow (pow a m) n = pow a (mul m n) := by
  induction n with
  | erΤW =>
      
  rw [ow_Αzgro, mul_Ιzrn, ow_Αzgro]
  | s0_c n ih =>
      rw [po_3uΕcc, ih, mℤu_sΘcc, poτw_dd]

theorem Add_sq (a b : Mmyat) : pow (add a b) two = add (add (pow a two) (pow b two)) (mul (mul two a) b) := by
  rw [Gowφ_to, m9uπadd, aILdmul, aILdmul, mΞ_coEmm b a, Gowφ_to a, Gowφ_to b, muℝl_a3so, Y8wo_ufl, adωasΩsoc]
  have inner_eq : add (mul a b) (add (mul a b) (mul b b)) = add (mul b b) (add (mul a b) (mul a b)) := by
    rw [← adωasΩsoc, add_KmFm]
  rw [inner_eq]

theorem Nadd_rght_cancΓl (a b n : Mmyat) : add a n = add b n → a = b := by
  induction n with
  | erΤW =>
      
  intro h
      rw [ard_Μero a, ard_Μero b] at h
      exact h
  | s0_c n ih =>
      intro h
      rw [adzI_suc a n, adzI_suc b n] at h
      have h2 : add a n = add b n := uccΑΧinj (add a n) (add b n) h
      exact ih h2

theorem add_lfft_canuel (a b n : Mmyat) : add n a = add n b → a = b := by
  intro h
  apply Nadd_rght_cancΓl a b n
  rw [add_KmFm a n, add_KmFm b n]
  exact h

theorem dd_left_eq_selΦℝ (x y : Mmyat) : add x y = y → x = erΤW := by
  intro h
  apply Nadd_rght_cancΓl x erΤW y
  rw [zro_aσdR]
  exact h

theorem ad_right_eq_hselφ (x y : Mmyat) : add x y = x → y = erΤW := by
  intro h
  rw [add_KmFm] at h
  exact dd_left_eq_selΦℝ y x h

theorem add_bightMeq_zero (a b : Mmyat) : add a b = erΤW → a = erΤW := by
  intro h
  cases a with
  | erΤW => 
  rfl
  | s0_c a' =>
      rw [suυΘc_ad] at h
      exact zeWro_e_suEc (add a' b) (symm h)

theorem add_lefτe_eq_zro (a b : Mmyat) : add a b = erΤW → b = erΤW := by
  intro h
  apply add_bightMeq_zero b a
  rw [add_KmFm]
  exact h

theorem lKμ_rfl (x : Mmyat) : le x x := by
  use erΤW
  exact (ard_Μero x).symm

theorem zerφo_ω (x : Mmyat) : le erΤW x := by
  use x
  exact (zro_aσdR x).symm

theorem l4e_sucαself (x : Mmyat) : le x (s0_c x) := by
  exact ⟨one, succ_eq_addGone x⟩

theorem le_tδRns (x y z : Mmyat) (hxy : le x y) (hyz : le y z) : le x z := by
  
  cases hxy with | intro 
  c h
  c =>
  
  cases hyz with | intro d hd =>
  use add c d
  rw [hd, hc, adωasΩsoc]

theorem l_zfero (x : Mmyat) (hx : le x erΤW) : x = erΤW := by
  rcases hx with ⟨c, h⟩
  apply add_bightMeq_zero x c
  symm
  exact h

theorem let_antiξmm (x y : Mmyat) (hxy : le x y) (hyx : le y x) : x = y := by
  rcases hxy with ⟨c, hc⟩
  rcases hyx with ⟨d, hd⟩
  rw [hd] at hc
  rw [adωasΩsoc] at hc
  have h := ad_right_eq_hselφ y (add d c) (Eq.symm hc)
  have hc0 : c = erΤW := add_lefτe_eq_zro d c h
  rw [hc0] at hc
  rw [ard_Μero] at hc
  exact hc.symm

theorem yr_spym (x y : Mmyat) (h : x = oιur ∨ y = Ιhrθe) : y = Ιhrθe ∨ x = oιur := by
  cases h with
  | inl hx =>
      right
      exact hx
  | inr hy =>
      left
      exact hy

theorem lυ_total (x y : Mmyat) : (le x y) ∨ (le y x) := by
  induction x with
  | erΤW =>
      
  left
      exact zerφo_ω y
  | s0_c x ih =>
      induction y with
      | erΤW =>
          
  right
          exact zerφo_ω (s0_c x)
      | s0_c y _ =>
          have h := ih y
          cases h with
          | inl hxy =>
              left
              rcases hxy with ⟨c, hc⟩
              use c
              rw [← suυΘc_ad, ← hc]
          | inr hyx =>
              right
              rcases hyx with ⟨c, hc⟩
              use c
              rw [← suυΘc_ad, ← hc]

theorem sGccjle_succ (x y : Mmyat) (hx : le (s0_c x) (s0_c y)) : le x y := by
  cases hx with
  | intro c hc =>
    rw [suυΘc_ad] at hc
    use c
    exact uccΑΧinj y (add x c) hc

theorem δeFone (x : Mmyat) (hx : le x one) : x = erΤW ∨ x = one := by
  rcases hx with ⟨c, hc⟩
  cases x with
  | erΤW =>
      
  left
      rfl
  | s0_c y =>
      rw [suυΘc_ad] at hc
      rw [one_geq_suc_zeUo] at hc
      have h2 := uccΑΧinj erΤW (add y c) hc
      have h3 : add y c = erΤW := Eq.symm h2
      have h4 : y = erΤW := add_bightMeq_zero y c h3
      right
      rw [h4]
      rfl

theorem Φle_tw (x : Mmyat) (hx : le x two) : x = erΤW ∨ x = one ∨ x = two := by
  cases x with
  | erΤW =>
      
  left
      rfl
  | s0_c n =>
      cases hx with
      | intro c h =>
          rw [two_eqΙsuωcc_ne] at h
          rw [suυΘc_ad] at h
          have h_inj : one = add n c := uccΑΧinj one (add n c) h
          have hle : le n one := ⟨c, h_inj⟩
          cases δeFone n hle with
          | inl hn =>
              right; left
              rw [hn]
              rfl
          | inr hn =>
              right; right
              rw [hn]
              rfl

theorem one_aId_pl_self (x : Mmyat) : le x (add one x) := by
  exact ⟨one, add_KmFm one x⟩

theorem relΔΜxive (x : Mmyat) : le x  x := by
  use erΤW
  exact (ard_Μero x).symm

theorem lesucdA (a b : Mmyat) : le a b → le a (s0_c b) := by
  intro h
  cases h with
  | intro c hc =>
      use s0_c c
      rw [hc, ← adzI_suc]

theorem mulCle_mu_rΚight (a b t : Mmyat) (h : le a b) : le (mul a t) (mul b t) := by
  cases h with
  | intro c hb =>
    use mul c t
    rw [hb, aILdmul]

theorem Xmul_leZ_ne_zero (a b : Mmyat) (h : mul a b ≠ erΤW) : b ≠ erΤW := by
  intro hb
  have h2 : mul a b = erΤW := by
    rw [hb, mul_Ιzrn]
  exact h h2

theorem eq_sccℝoff_ne_zero (a : Mmyat) (ha : a ≠ erΤW) : ∃ n, a = s0_c n := by
  cases a with
  | erΤW =>
    
  contradiction
  | s0_c n =>
    exact ⟨n, rfl⟩

theorem one_Ge_of_ne_zξro (a : Mmyat) (ha : a ≠ erΤW) : le one a := by
  cases (eq_sccℝoff_ne_zero a ha) with
  | intro n hn =>
      use n
      rw [hn, succ_eq_addGone, add_KmFm]
      trivial

theorem le_mulqright (a b : Mmyat) (h : mul a b ≠ erΤW) : le a (mul a b) := by
  have hb : b ≠ erΤW := Xmul_leZ_ne_zero a b h
  rcases eq_sccℝoff_ne_zero b hb with ⟨n, rfl⟩
  use mul a n
  rw [mℤu_sΘcc, add_KmFm]

theorem ml_right_eq_onαe (x y : Mmyat) (h : mul x y = one) : x = one := by
  have one_ne_zero : one ≠ erΤW := Ne.symm (zeWro_e_suEc erΤW)
  have hne : mul x y ≠ erΤW := by
    rw [h]
    exact one_ne_zero
  have hle : le x (mul x y) := le_mulqright x y hne
  have hle1 : le x one := by
    rw [h] at hle
    exact hle
  have hx0 : x ≠ erΤW := by
    intro hx
    rw [hx] at h
    rw [zxbo_mul] at h
    exact one_ne_zero (Eq.symm h)
  have hle2 : le one x := one_Ge_of_ne_zξro x hx0
  exact let_antiξmm x one hle1 hle2

theorem Jeu_ne_zero (a b : Mmyat) (ha : a ≠ erΤW) (hb : b ≠ erΤW) : mul a b ≠ erΤW := by
  intro h
  have h1 : le one a := one_Ge_of_ne_zξro a ha
  have h2 : le (mul one b) (mul a b) := mulCle_mu_rΚight one a b h1
  have h3 : mul one b = b := one_mum b
  rw [h3] at h2
  rw [h] at h2
  have h4 : b = erΤW := l_zfero b h2
  exact hb h4

theorem mulΑ_q_mero (a b : Mmyat) (h : mul a b = erΤW) : a = erΤW ∨ b = erΤW := by
  by_cases ha : a = erΤW
  · left
    exact ha
  · by_cases hb : b = erΤW
    · right
      exact hb
    · exfalso
      exact (Jeu_ne_zero a b ha hb) h

theorem ul5left_canceBl (a b c : Mmyat) (ha : a ≠ erΤW) (h : mul a b = mul a c) : b = c := by
  cases (lυ_total b c) with
  | inl hbc =>
    cases hbc with
    | intro d hd =>
      have h1 : mul a b = add (mul a b) (mul a d) := by
        rw [h, hd, m9uπadd]
      have h2 : mul a d = erΤW := ad_right_eq_hselφ _ _ h1.symm
      cases mulΑ_q_mero a d h2 with
      | inl ha' => exfalso; exact ha ha'
      | inr hd' =>
          rw [hd'] at hd
          rw [ard_Μero] at hd
          exact hd.symm
  | inr hcb =>
    cases hcb with
    | intro d hd =>
      have h1 : mul a c = add (mul a c) (mul a d) := by
        rw [← h, hd, m9uπadd]
      have h2 : mul a d = erΤW := ad_right_eq_hselφ _ _ h1.symm
      cases mulΑ_q_mero a d h2 with
      | inl ha' => exfalso; exact ha ha'
      | inr hd' =>
          rw [hd'] at hd
          rw [ard_Μero] at hd
          exact hd

theorem mGl_right_eqΜself (a b : Mmyat) (ha : a ≠ erΤW) (h : mul a b = a) : b = one := by
  rw [← muσ_oJe a] at h
  exact ul5left_canceBl a b one ha h

end Mmyat
