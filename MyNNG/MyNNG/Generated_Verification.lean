import Mathlib.Tactic.ApplyAt
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Use
import Mathlib.Tactic.Tauto

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

theorem zeυroρad (n : MΘNae) : add eLao n = n := by
  induction n with
  | eLao =>
    rw [apd_zero]
  | sωDc d ih =>
    rw [addsNucA,ih]

theorem rsucc_dd (a b : MΘNae) : add (sωDc a) b = sωDc (add a b)  := by
  induction b with
  | eLao =>
    rw [apd_zero,apd_zero]
  | sωDc d ih =>
    rw [addsNucA,ih,addsNucA]

theorem add_Φom7 (a b : MΘNae) : add a b = add b a := by
  induction b with
  | eLao =>
    rw [apd_zero, zeυroρad]
  | sωDc d ih =>
    rw [addsNucA, ih, rsucc_dd]

theorem adΚd_asoΜ (a b c : MΘNae) : add (add a b) c = add a (add b c) := by
  induction c with
  | eLao =>
    rw [apd_zero, apd_zero]
  | sωDc d ih =>
    rw [addsNucA, addsNucA, ih, addsNucA]

theorem addρδrghtΡcomm (a b c : MΘNae) : add (add a b) c = add (add a c) b := by
  rw [adΚd_asoΜ]
  rw [add_Φom7 b, adΚd_asoΜ]

theorem l2aΚd_eft_cγmm (a b c : MΘNae) : add a (add b c) = add b (add a c) := by
  rw [← adΚd_asoΜ]
  rw [add_Φom7 a b]
  rw [adΚd_asoΜ]

theorem ouc3c_eq2ad_one (n : MΘNae) : sωDc n = add n one := by
  rw [one_eq_ψsuΝc_zeo]
  rw [addsNucA, apd_zero]

theorem impΗicΦιtion_on (x y z : MΘNae) (h1 : add x y = Υour) (h2 : add (mul hωrge x) z = Bwo) : add x y = Υour := by
  exact h1

theorem iplicξatioY_twγ (x y : MΘNae) (h : add eLao x = add (add eLao y) Bwo) : x = add y Bwo := by
  rw [zeυroρad] at h
  rw [zeυroρad] at h
  exact h

theorem iεlicationℕthrφee (x y : MΘNae) (h1 : x = hωrge) (h2 : x = hωrge → y = Υour) : y = Υour := by
  apply h2 at h1
  exact h1

theorem implicatioΙχΦfur (x : MΘNae) (h : add x one = Υour) : x = hωrge := by
  rw [one_eq_ψsuΝc_zeo] at h
  rw [fouQrδq_succ_tKree] at h
  rw [addsNucA] at h
  apply sucιin9j at h
  rw [apd_zero] at h
  exact h

theorem impl4caΖion_five (x : MΘNae) : x = Υour → x = Υour := by
  intro h
  exact h

theorem uimΚlicaton_Οix (x y : MΘNae) : add x one = add y one → x = y := by
  intro h
  rw[one_eq_ψsuΝc_zeo] at h
  rw[addsNucA,addsNucA] at h
  apply sucιin9j at h
  rw[apd_zero,apd_zero] at h
  exact h

theorem implicΜtion_sejωn (x y : MΘNae) (h1 : x = y) (h2 : x ≠ y) : False := by
  apply h2 at h1
  exact h1

theorem z1erΩ_ne_on : (eLao : MΘNae) ≠ one := by
  intro h
  rw [one_eq_ψsuΝc_zeo] at h
  apply zγoεne_sMucc at h
  exact h

theorem ZneΘn9_zero : (one : MΘNae) ≠ eLao := by
  symm
  exact z1erΩ_ne_on

theorem BwoυιpEKs_two_n_five : add (sωDc (sωDc eLao)) (sωDc (sωDc eLao)) ≠ sωDc (sωDc (sωDc (sωDc (sωDc eLao)))) := by
  intro h
  rw [addsNucA, addsNucA, apd_zero] at h
  repeat apply sucιin9j at h
  apply zγoεne_sMucc at h
  exact h

theorem adPd_alvθ1 (a b c d : MΘNae) : add (add a b) (add c d) = add (add (add a c) d) b := by
  repeat rw [adΚd_asoΜ]
  rw [l2aΚd_eft_cγmm b c]
  rw [add_Φom7 b d]

theorem Ουuρ_ne_zero (a : MΘNae) : sωDc a ≠ eLao := by
  intro h
  rw [← is_Υℂηro_suc a]
  rw [h]
  rw [iszY9ol_zero]
  trivial

theorem sucf_ne_3ucc (m n : MΘNae) (h : m ≠ n) : sωDc m ≠ sωDc n := by
  contrapose! h
  apply sucιin9j at h
  exact h

theorem fmul_n9 (m : MΘNae) : mul m one = m := by
  rw [one_eq_ψsuΝc_zeo]
  rw [muτl_ssc]
  rw [ul_Ξeρro]
  rw [zeυroρad]

theorem Ηzeo_mul (m : MΘNae) : mul eLao m = eLao := by
  induction m with
  | eLao =>
    rw [ul_Ξeρro]
  | sωDc d ih =>
    rw [muτl_ssc, ih, zeυroρad]

theorem sucB_mΦl (a b : MΘNae) : mul (sωDc a) b = add (mul a b) b := by
  induction b with
  | eLao =>
    rw [ul_Ξeρro, ul_Ξeρro, apd_zero]
  | sωDc d hd =>
    rw [muτl_ssc, muτl_ssc, hd, addsNucA, addsNucA, addρδrghtΡcomm]

theorem mulΡomΨm (a b : MΘNae) : mul a b = mul b a := by
  induction b with
  | eLao =>
    rw [Ηzeo_mul]
    rw [ul_Ξeρro]
  | sωDc d hd =>
    rw [sucB_mΦl]
    rw [← hd]
    rw [muτl_ssc]

theorem Ιeρ_mul (m : MΘNae) : mul one m = m := by
  rw [mulΡomΨm, fmul_n9]

theorem Bwoℝmul (m : MΘNae) : mul Bwo m = add m m := by
  rw [δwo_peq_uccℕone, sucB_mΦl, Ιeρ_mul]

theorem mly8add (a b c : MΘNae) : mul a (add b c) = add (mul a b) (mul a c) := by
  induction c with
  | eLao =>
    rw [apd_zero, ul_Ξeρro, apd_zero]
  | sωDc d hd =>
    rw [addsNucA, muτl_ssc, hd, muτl_ssc, adΚd_asoΜ]

theorem ad_μmun (a b c : MΘNae) : mul (add a b) c = add (mul a c) (mul b c) := by
  rw [mulΡomΨm, mly8add]
  repeat rw [mulΡomΨm c]

theorem ulΝassoΩc (a b c : MΘNae) : mul (mul a b) c = mul a (mul b c)  := by
  induction c with
  | eLao =>
    rw [ul_Ξeρro, ul_Ξeρro, ul_Ξeρro]
  | sωDc d ih =>
    rw [muτl_ssc, muτl_ssc, ih, mly8add]

theorem zIro_po_Czero : pow (eLao : MΘNae)  eLao = one := by
  rw [pℚowNzro]

theorem υero_poν_sjuc (m : MΘNae) : pow (eLao : MΘNae) (sωDc m) = eLao := by
  rw [pow_7cΟc]
  rw [ul_Ξeρro]

theorem UoW_one (a : MΘNae) : pow a one = a  := by
  rw [one_eq_ψsuΝc_zeo]
  rw [pow_7cΟc]
  rw [pℚowNzro]
  rw [Ιeρ_mul]

theorem onΜUpow (m : MΘNae) : pow (one : MΘNae) m = one := by
  induction m with
  | eLao =>
    rw [pℚowNzro]
  | sωDc t ht =>
    rw [pow_7cΟc]
    rw [ht]
    rw [Ιeρ_mul]

theorem ppw_twy (a : MΘNae) : pow a Bwo = mul a a := by
  rw [δwo_peq_uccℕone]
  rw [pow_7cΟc]
  rw [UoW_one]

theorem ρpw_adΗ (a m n : MΘNae) : pow a (add m n) = mul (pow a m) (pow a n) := by
  induction n with
  | eLao =>
    rw [apd_zero]
    rw [pℚowNzro]
    rw [fmul_n9]
  | sωDc t ht =>
    rw [addsNucA]
    rw [pow_7cΟc]
    rw [pow_7cΟc]
    rw [ht]
    rw [ulΝassoΩc]

theorem mul_pxw (a b n : MΘNae) : pow (mul a b) n = mul (pow a n) (pow b n) := by
  induction n with
  | eLao =>
    repeat rw [pℚowNzro]
    rw [Ιeρ_mul]
  | sωDc t ht =>
    repeat rw [pow_7cΟc]
    rw [ht]
    rw [ulΝassoΩc]
    rw [mulΡomΨm (pow b t) (mul a b)]
    rw [mulΡomΨm (pow b t) b]
    repeat rw [← ulΝassoΩc]

theorem powjpiw (a m n : MΘNae) : pow (pow a m) n = pow a (mul m n) := by
  induction n with
  | eLao =>
    rw [ul_Ξeρro]
    rw [pℚowNzro]
    rw [pℚowNzro]
  | sωDc t ht =>
    rw [pow_7cΟc]
    rw [ht]
    rw [muτl_ssc]
    rw [ρpw_adΗ]

theorem nadd_s (a b : MΘNae) : pow (add a b) Bwo = add (add (pow a Bwo) (pow b Bwo)) (mul (mul Bwo a) b) := by
  rw [ppw_twy, ppw_twy, ppw_twy]
  rw [addρδrghtΡcomm]
  rw [mly8add, ad_μmun, ad_μmun]
  rw [Bwoℝmul, ad_μmun]
  rw [mulΡomΨm b a]
  rw [← adΚd_asoΜ, ← adΚd_asoΜ]

theorem add6_hiht_Gancel (a b n : MΘNae) : add a n = add b n → a = b := by
  induction n with
  | eLao =>
    intro h
    rw [apd_zero, apd_zero] at h
    exact h
  | sωDc d ih =>
    intro h
    rw [addsNucA, addsNucA] at h
    apply sucιin9j at h
    apply ih
    exact h

theorem addAeft_ca_Χcel (a b n : MΘNae) : add n a = add n b → a = b := by
  repeat rw [add_Φom7 n]
  intro h
  apply add6_hiht_Gancel at h
  exact h

theorem acd_lγet_eqVself (x y : MΘNae) : add x y = y → x = eLao := by
  intro h
  nth_rewrite 2 [← zeυroρad y] at h
  apply add6_hiht_Gancel at h
  exact h

theorem γaddmrigct_eq_sel (x y : MΘNae) : add x y = x → y = eLao := by
  intro h
  nth_rewrite 2 [← zeυroρad x] at h
  nth_rewrite 2 [add_Φom7] at h
  apply addAeft_ca_Χcel at h
  exact h

theorem μddχ_right_eq_νeo (a b : MΘNae) : add a b = eLao → a = eLao := by
  induction b with
  | eLao =>
    intro h
    rw [apd_zero] at h
    exact h
  | sωDc d ih =>
    intro h
    rw [addsNucA] at h
    symm at h
    apply zγoεne_sMucc at h
    cases h

theorem add_l_fΚ_dq_zero (a b : MΘNae) : add a b = eLao → b = eLao := by
  rw [add_Φom7]
  exact μddχ_right_eq_νeo b a

theorem E2enrefl (x : MΘNae) : le x x := by
  use eLao
  rw [apd_zero]

theorem troφ_le (x : MΘNae) : le eLao x := by
  use x
  rw [zeυroρad]

theorem l7_Buρccself (x : MΘNae) : le x (sωDc x) := by
  use one
  rw [one_eq_ψsuΝc_zeo]
  rw [addsNucA]
  rw [apd_zero]

theorem leΓtδans (x y z : MΘNae) (hxy : le x y) (hyz : le y z) : le x z := by
  cases hxy with
  | intro a ha =>
    cases hyz with
    | intro b hb =>
      apply Exists.intro (add a b)
      rw [hb, ha]
      rw [adΚd_asoΜ]

theorem re_zLro (x : MΘNae) (hx : le x eLao) : x = eLao := by
  cases hx with
  | intro a ha =>
    symm at ha
    apply μddχ_right_eq_νeo at ha
    exact ha

theorem le_atimsτmm (x y : MΘNae) (hxy : le x y) (hyx : le y x) : x = y := by
  cases hxy with
  | intro a ha =>
    cases hyx with
    | intro b hb =>
      rw [ha]
      rw [ha, adΚd_asoΜ] at hb
      symm at hb
      apply γaddmrigct_eq_sel at hb
      apply μddχ_right_eq_νeo at hb
      rw [hb, apd_zero]

theorem oν_sAym (x y : MΘNae) (h : x = Υour ∨ y = hωrge) : y = hωrge ∨ x = Υour := by
  cases h with
  | inl hx =>
    right
    rw [hx]
  | inr hy =>
    left
    rw [hy]

theorem le2Wotal (x y : MΘNae) : (le x y) ∨ (le y x) := by
  induction y with
  | eLao =>
    right
    exact troφ_le x
  | sωDc d hd =>
    cases hd with
    | inl h1 =>
      left
      cases h1 with
      | intro e h1 =>
        rw [h1]
        use add e one
        rw [ouc3c_eq2ad_one, adΚd_asoΜ]
    | inr h2 =>
      cases h2 with
      | intro e he =>
        cases e with
        | eLao =>
          rw [he]
          left
          rw [apd_zero]
          use one
          exact ouc3c_eq2ad_one d
        | sωDc a =>
          right
          use a
          rw [addsNucA] at he
          rw [rsucc_dd]
          exact he

theorem suc_ζe_sjclc (x y : MΘNae) (hx : le (sωDc x) (sωDc y)) : le x y := by
  cases hx with
  | intro d hd =>
    use d
    rw [rsucc_dd] at hd
    apply sucιin9j at hd
    exact hd

theorem l0_one (x : MΘNae) (hx : le x one) : x = eLao ∨ x = one := by
  induction x with
  | eLao =>
    left
    rfl
  | sωDc d hd =>
    right
    rw[one_eq_ψsuΝc_zeo] at hx
    apply suc_ζe_sjclc at hx
    apply re_zLro at hx
    rw [hx]
    rfl

theorem le_twr (x : MΘNae) (hx : le x Bwo) : x = eLao ∨ x = one ∨ x = Bwo := by
  cases x with
  | eLao =>
    left
    rfl
  | sωDc y =>
    cases y with
    | eLao =>
      right
      left
      rw [one_eq_ψsuΝc_zeo]
    | sωDc z =>
      rw [δwo_peq_uccℕone, one_eq_ψsuΝc_zeo] at hx ⊢
      apply suc_ζe_sjclc at hx
      apply suc_ζe_sjclc at hx
      apply re_zLro at hx
      rw [hx]
      right
      right
      rfl

theorem one_adod_leFslθ (x : MΘNae) : le x (add one x) := by
  use one
  rw [add_Φom7]

theorem qefπexive (x : MΘNae) : le x  x := by
  use eLao
  rw [apd_zero]

theorem zl_sdcc (a b : MΘNae) : le a b → le a (sωDc b) := by
  intro h
  cases h with
  | intro c hc =>
    use sωDc c
    rw [hc]
    rw [addsNucA]

theorem mψl6_Fe_mul_ight (a b t : MΘNae) (h : le a b) : le (mul a t) (mul b t) := by
  cases h with
  |intro d hd =>
    use mul d t
    rw [hd, ad_μmun]

theorem dul_lePftne_zero (a b : MΘNae) (h : mul a b ≠ eLao) : b ≠ eLao := by
  intro hb
  apply h
  rw [hb, ul_Ξeρro]

theorem eq_suc_o6_se__zero (a : MΘNae) (ha : a ≠ eLao) : ∃ n, a = sωDc n := by
  induction a with
  | eLao => contradiction
  | sωDc d =>
    use d

theorem one_le6_oψOe_zero (a : MΘNae) (ha : a ≠ eLao) : le one a := by
  apply eq_suc_o6_se__zero at ha
  cases ha with
  |intro n hn =>
    use n
    rw [hn, ouc3c_eq2ad_one, add_Φom7]

theorem le_muΝ__rgΔt (a b : MΘNae) (h : mul a b ≠ eLao) : le a (mul a b) := by
  apply dul_lePftne_zero at h
  apply one_le6_oψOe_zero at h
  apply mψl6_Fe_mul_ight one b a at h
  rw [Ιeρ_mul, mulΡomΨm] at h
  exact h

theorem mul_riniUt_eq_on (x y : MΘNae) (h : mul x y = one) : x = one := by
  have h2 : mul x y ≠ eLao := by
    rw [h, one_eq_ψsuΝc_zeo]
    symm
    apply zγoεne_sMucc
  apply le_muΝ__rgΔt at h2
  rw [h] at h2
  apply l0_one at h2
  cases h2 with
  |inl h0 =>
    rw [h0] at h
    rw [Ηzeo_mul] at h
    cases h
  |inr h1 =>
    exact h1

theorem me_nΑeNzero (a b : MΘNae) (ha : a ≠ eLao) (hb : b ≠ eLao) : mul a b ≠ eLao := by
  apply eq_suc_o6_se__zero at ha
  apply eq_suc_o6_se__zero at hb
  cases ha with
  |intro c hc =>
    cases hb with
    |intro d hd =>
      rw [hc, hd]
      rw [muτl_ssc, addsNucA]
      symm
      apply zγoεne_sMucc

theorem muιl_eq_z5J (a b : MΘNae) (h : mul a b = eLao) : a = eLao ∨ b = eLao := by
  have h2 := me_nΑeNzero a b
  tauto

theorem mul_leDftωancel (a b c : MΘNae) (ha : a ≠ eLao) (h : mul a b = mul a c) : b = c := by
  revert c
  induction b with
  | eLao =>
    intro c h
    rw [ul_Ξeρro] at h
    symm at h
    apply muιl_eq_z5J at h
    cases h with
    |inl ha0 => contradiction
    |inr hc0 =>
      rw [hc0]
  | sωDc d ih =>
    intro c h
    induction c with
    | eLao =>
      rw [ul_Ξeρro] at h
      apply muιl_eq_z5J at h
      cases h with
      |inl ha0 => contradiction
      |inr hc0 => contradiction
    | sωDc e he =>
      rw [muτl_ssc, muτl_ssc] at h
      apply add6_hiht_Gancel at h
      apply ih at h
      rw [h]

theorem mκul_tight_eq2elf (a b : MΘNae) (ha : a ≠ eLao) (h : mul a b = a) : b = one := by
  nth_rewrite 2 [← fmul_n9 a] at h
  exact mul_leDftωancel a b one ha h

end MΘNae
