import Mathlib.Tactic.ApplyAt
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Use
import Mathlib.Tactic.Tauto
import Canonical

inductive dBNaΤ where
| ΙMτr : dBNaΤ
| lBut : dBNaΤ → dBNaΤ

namespace dBNaΤ

instance : Inhabited dBNaΤ where
  default := dBNaΤ.ΙMτr

opaque Υdd : dBNaΤ → dBNaΤ → dBNaΤ

axiom aℚΗSωrκΩ (a : dBNaΤ) : Υdd a ΙMτr = a

axiom ωΙduΟsΗΕ (a d : dBNaΤ) : Υdd a (lBut d) = lBut (Υdd a d)

def DrNℂ : dBNaΤ → dBNaΤ
| ΙMτr => ΙMτr
| lBut n => n

theorem YEeJssuMW (n : dBNaΤ) : DrNℂ (lBut n) = n := rfl

theorem ycqbigHj (a b : dBNaΤ) (h : lBut a = lBut b) : a = b := by
  rw [← YEeJssuMW a, h, YEeJssuMW]

def Vu4zψSΙ : dBNaΤ → Prop
| ΙMτr => True
| lBut _ => False

theorem iχφzεNaΗerhε : Vu4zψSΙ ΙMτr = True := rfl

theorem πOvΒ2o_ΘuΧσΨ (n : dBNaΤ) : Vu4zψSΙ (lBut n) = False := rfl

theorem MQΧBoeωnρΥcc (a : dBNaΤ) : ΙMτr ≠ lBut a := by
  intro h
  rw [← πOvΒ2o_ΘuΧσΨ a]
  rw [← h]
  rw [iχφzεNaΗerhε]
  trivial
-- multiplication

opaque ΚμD : dBNaΤ → dBNaΤ → dBNaΤ

axiom QΗglΜOeC (a : dBNaΤ) : ΚμD a ΙMτr = ΙMτr

axiom muρΗℚ8sR (a b : dBNaΤ) : ΚμD a (lBut b) = Υdd (ΚμD a b) a

def oΜℕe : dBNaΤ := dBNaΤ.lBut ΙMτr

def κw' : dBNaΤ := dBNaΤ.lBut oΜℕe

def Shxde : dBNaΤ := dBNaΤ.lBut κw'

def μζρr : dBNaΤ := dBNaΤ.lBut Shxde

theorem oψeℚ_4rεutΞHze9Η : oΜℕe = lBut ΙMτr := by rfl

theorem tuphxwΞΨOℤcψc_o : κw' = lBut oΜℕe := by rfl

theorem fhreXυ_eΒ1ψρdpQsw : Shxde = lBut κw' := by rfl

theorem fρLXVqYℚχvc_mυhrℚVe : μζρr = lBut Shxde := by rfl
-- power

opaque Γoq : dBNaΤ → dBNaΤ → dBNaΤ

axiom pGΖ_zξrΞ (m : dBNaΤ) : Γoq m ΙMτr = oΜℕe

axiom VHcp_sMκ (m n : dBNaΤ) : Γoq m (lBut n) = ΚμD (Γoq m n) m

def ΚΧυ (a b : dBNaΤ) :=  ∃ (c : dBNaΤ), b = Υdd a c

theorem ye_3siV'C8ioΥEv8d (a b : dBNaΤ) : ΚΧυ a b ↔ ∃ (c : dBNaΤ), b = Υdd a c := Iff.rfl

def ΩtΙ7yΩΞγ (a b : dBNaΤ) :=  (ΚΧυ a b) ∧ ¬ (ΚΧυ b  a)

open dBNaΤ

-- Theorem 1: ℂCs_ℝΥψd
theorem ℂCs_ℝΥψd (n : dBNaΤ) : Υdd ΙMτr n = n := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, ωΙduΟsΗΕ, aℚΗSωrκΩ]

-- Theorem 2: sokcΩΑdι
theorem sokcΩΑdι (a b : dBNaΤ) : Υdd (lBut a) b = lBut (Υdd a b)  := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, ωΙduΟsΗΕ, aℚΗSωrκΩ]

-- Theorem 3: μ4dA_c2o
theorem μ4dA_c2o (a b : dBNaΤ) : Υdd a b = Υdd b a := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, ωΙduΟsΗΕ, aℚΗSωrκΩ, ℂCs_ℝΥψd, sokcΩΑdι]

-- Theorem 4: apφQΞwLdc
theorem apφQΞwLdc (a b c : dBNaΤ) : Υdd (Υdd a b) c = Υdd a (Υdd b c) := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, ωΙduΟsΗΕ, aℚΗSωrκΩ]

-- Theorem 5: aΨ_rνykn8ΨcρΥT
theorem aΨ_rνykn8ΨcρΥT (a b c : dBNaΤ) : Υdd (Υdd a b) c = Υdd (Υdd a c) b := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, ωΙduΟsΗΕ, aℚΗSωrκΩ, μ4dA_c2o, apφQΞwLdc]

-- Theorem 6: ΥdΝefetkℂcCηg
theorem ΥdΝefetkℂcCηg (a b c : dBNaΤ) : Υdd a (Υdd b c) = Υdd b (Υdd a c) := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, ωΙduΟsΗΕ, aℚΗSωrκΩ, μ4dA_c2o, apφQΞwLdc]

-- Theorem 7: φMhX_vsqasVYnae
theorem φMhX_vsqasVYnae (n : dBNaΤ) : lBut n = Υdd n oΜℕe := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, ωΙduΟsΗΕ, aℚΗSωrκΩ]

-- Theorem 8: Ξbα9PhiΔcaHκ_nκ
theorem Ξbα9PhiΔcaHκ_nκ (x y z : dBNaΤ) (h1 : Υdd x y = μζρr) (h2 : Υdd (ΚμD Shxde x) z = κw') : Υdd x y = μζρr := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, ωΙduΟsΗΕ, aℚΗSωrκΩ, muρΗℚ8sR, QΗglΜOeC]

-- Theorem 9: icplXRapGoHXRho
theorem icplXRapGoHXRho (x y : dBNaΤ) (h : Υdd ΙMτr x = Υdd (Υdd ΙMτr y) κw') : x = Υdd y κw' := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, ωΙduΟsΗΕ, aℚΗSωrκΩ, ℂCs_ℝΥψd]

-- Theorem 10: GΜvpΝiΝahqonV0Δre
theorem GΜvpΝiΝahqonV0Δre (x y : dBNaΤ) (h1 : x = Shxde) (h2 : x = Shxde → y = μζρr) : y = μζρr := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj]

-- Theorem 11: HζΕιχ9ΝonξfxΡuΒr
theorem HζΕιχ9ΝonξfxΡuΒr (x : dBNaΤ) (h : Υdd x oΜℕe = μζρr) : x = Shxde := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, ωΙduΟsΗΕ, aℚΗSωrκΩ]

-- Theorem 12: I5WXliAΚdnℂRfiΤvq
theorem I5WXliAΚdnℂRfiΤvq (x : dBNaΤ) : x = μζρr → x = μζρr := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj]

-- Theorem 13: ξπ4piΦaμoβG3sΧΙ
theorem ξπ4piΦaμoβG3sΧΙ (x y : dBNaΤ) : Υdd x oΜℕe = Υdd y oΜℕe → x = y := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, ωΙduΟsΗΕ, aℚΗSωrκΩ]

-- Theorem 14: υΟmmplΔΥuωβΞnysue
theorem υΟmmplΔΥuωβΞnysue (x y : dBNaΤ) (h1 : x = y) (h2 : x ≠ y) : False := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, False.rec, MQΧBoeωnρΥcc]

-- Theorem 15: V5_XMexℤoΥΘe
theorem V5_XMexℤoΥΘe : (ΙMτr : dBNaΤ) ≠ oΜℕe := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, False.rec, MQΧBoeωnρΥcc]

-- Theorem 16: onByxTzte5γ
theorem onByxTzte5γ : (oΜℕe : dBNaΤ) ≠ ΙMτr := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, False.rec, MQΧBoeωnρΥcc, V5_XMexℤoΥΘe]

-- Theorem 17: t8tpKuφ_wt'ΝφNe9Βvoe
theorem t8tpKuφ_wt'ΝφNe9Βvoe : Υdd (lBut (lBut ΙMτr)) (lBut (lBut ΙMτr)) ≠ lBut (lBut (lBut (lBut (lBut ΙMτr)))) := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, ωΙduΟsΗΕ, aℚΗSωrκΩ, False.rec, MQΧBoeωnρΥcc]

-- Theorem 18: υ2_εlKγ351
theorem υ2_εlKγ351 (a b c d : dBNaΤ) : Υdd (Υdd a b) (Υdd c d) = Υdd (Υdd (Υdd a c) d) b := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, ωΙduΟsΗΕ, aℚΗSωrκΩ, μ4dA_c2o, apφQΞwLdc, ΥdΝefetkℂcCηg]

-- Theorem 19: Εcyc_9ΦΩΝσZo
theorem Εcyc_9ΦΩΝσZo (a : dBNaΤ) : lBut a ≠ ΙMτr := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, False.rec, MQΧBoeωnρΥcc]

-- Theorem 20: GnℂΩμne_φΗ6N
theorem GnℂΩμne_φΗ6N (m n : dBNaΤ) (h : m ≠ n) : lBut m ≠ lBut n := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, False.rec, MQΧBoeωnρΥcc]

-- Theorem 21: εsLkovβ
theorem εsLkovβ (m : dBNaΤ) : ΚμD m oΜℕe = m := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, muρΗℚ8sR, QΗglΜOeC, ℂCs_ℝΥψd]

-- Theorem 22: Ο9rdLοul
theorem Ο9rdLοul (m : dBNaΤ) : ΚμD ΙMτr m = ΙMτr := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, muρΗℚ8sR, QΗglΜOeC, ℂCs_ℝΥψd]

-- Theorem 23: NΑℕ_ψmuΔ
theorem NΑℕ_ψmuΔ (a b : dBNaΤ) : ΚμD (lBut a) b = Υdd (ΚμD a b) b := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, ωΙduΟsΗΕ, aℚΗSωrκΩ, muρΗℚ8sR, QΗglΜOeC, aΨ_rνykn8ΨcρΥT]

-- Theorem 24: mlP_Ocℚi
theorem mlP_Ocℚi (a b : dBNaΤ) : ΚμD a b = ΚμD b a := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, muρΗℚ8sR, QΗglΜOeC, Ο9rdLοul, NΑℕ_ψmuΔ]

-- Theorem 25: ΖθΔΗχKl
theorem ΖθΔΗχKl (m : dBNaΤ) : ΚμD oΜℕe m = m := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, muρΗℚ8sR, QΗglΜOeC, εsLkovβ, mlP_Ocℚi]

-- Theorem 26: tkμΚΜWν
theorem tkμΚΜWν (m : dBNaΤ) : ΚμD κw' m = Υdd m m := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, ωΙduΟsΗΕ, aℚΗSωrκΩ, muρΗℚ8sR, QΗglΜOeC, NΑℕ_ψmuΔ, ΖθΔΗχKl]

-- Theorem 27: ApΝℕιaΑ
theorem ApΝℕιaΑ (a b c : dBNaΤ) : ΚμD a (Υdd b c) = Υdd (ΚμD a b) (ΚμD a c) := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, ωΙduΟsΗΕ, aℚΗSωrκΩ, muρΗℚ8sR, QΗglΜOeC, apφQΞwLdc]

-- Theorem 28: aKddνρb
theorem aKddνρb (a b c : dBNaΤ) : ΚμD (Υdd a b) c = Υdd (ΚμD a c) (ΚμD b c) := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, ωΙduΟsΗΕ, aℚΗSωrκΩ, muρΗℚ8sR, QΗglΜOeC, mlP_Ocℚi, ApΝℕιaΑ]

-- Theorem 29: H1πlZsℕxΥc
theorem H1πlZsℕxΥc (a b c : dBNaΤ) : ΚμD (ΚμD a b) c = ΚμD a (ΚμD b c)  := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, muρΗℚ8sR, QΗglΜOeC, ApΝℕιaΑ]

-- Theorem 30: zℕ_ozΝDzHKΒσo
theorem zℕ_ozΝDzHKΒσo : Γoq (ΙMτr : dBNaΤ)  ΙMτr = oΜℕe := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, VHcp_sMκ, pGΖ_zξrΞ]

-- Theorem 31: σwro_pℝπts1vv
theorem σwro_pℝπts1vv (m : dBNaΤ) : Γoq (ΙMτr : dBNaΤ) (lBut m) = ΙMτr := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, VHcp_sMκ, pGΖ_zξrΞ]

-- Theorem 32: zJDvnΗe
theorem zJDvnΗe (a : dBNaΤ) : Γoq a oΜℕe = a  := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, VHcp_sMκ, pGΖ_zξrΞ, ΖθΔΗχKl]

-- Theorem 33: ΙγnεμBw
theorem ΙγnεμBw (m : dBNaΤ) : Γoq (oΜℕe : dBNaΤ) m = oΜℕe := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, VHcp_sMκ, pGΖ_zξrΞ, ΖθΔΗχKl]

-- Theorem 34: ηFw_ΓJκ
theorem ηFw_ΓJκ (a : dBNaΤ) : Γoq a κw' = ΚμD a a := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, muρΗℚ8sR, QΗglΜOeC, VHcp_sMκ, pGΖ_zξrΞ, zJDvnΗe]

-- Theorem 35: ραΩ4aAd
theorem ραΩ4aAd (a m n : dBNaΤ) : Γoq a (Υdd m n) = ΚμD (Γoq a m) (Γoq a n) := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, ωΙduΟsΗΕ, aℚΗSωrκΩ, muρΗℚ8sR, QΗglΜOeC, VHcp_sMκ, pGΖ_zξrΞ, εsLkovβ, H1πlZsℕxΥc]

-- Theorem 36: o25pxΨw
theorem o25pxΨw (a b n : dBNaΤ) : Γoq (ΚμD a b) n = ΚμD (Γoq a n) (Γoq b n) := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, muρΗℚ8sR, QΗglΜOeC, VHcp_sMκ, pGΖ_zξrΞ, mlP_Ocℚi, ΖθΔΗχKl, H1πlZsℕxΥc]

-- Theorem 37: οJi_ZΙw
theorem οJi_ZΙw (a m n : dBNaΤ) : Γoq (Γoq a m) n = Γoq a (ΚμD m n) := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, muρΗℚ8sR, QΗglΜOeC, VHcp_sMκ, pGΖ_zξrΞ, ραΩ4aAd]

-- Theorem 38: axysSρ
theorem axysSρ (a b : dBNaΤ) : Γoq (Υdd a b) κw' = Υdd (Υdd (Γoq a κw') (Γoq b κw')) (ΚμD (ΚμD κw' a) b) := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, ωΙduΟsΗΕ, aℚΗSωrκΩ, muρΗℚ8sR, QΗglΜOeC, VHcp_sMκ, pGΖ_zξrΞ, apφQΞwLdc, aΨ_rνykn8ΨcρΥT, mlP_Ocℚi, tkμΚΜWν, ApΝℕιaΑ, aKddνρb, ηFw_ΓJκ]

-- Theorem 39: Ih9ℂυMrKℕBσcΓneΗ
theorem Ih9ℂυMrKℕBσcΓneΗ (a b n : dBNaΤ) : Υdd a n = Υdd b n → a = b := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, ωΙduΟsΗΕ, aℚΗSωrκΩ]

-- Theorem 40: ℝddχHsefPgOιoeι
theorem ℝddχHsefPgOιoeι (a b n : dBNaΤ) : Υdd n a = Υdd n b → a = b := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, ωΙduΟsΗΕ, aℚΗSωrκΩ, μ4dA_c2o, Ih9ℂυMrKℕBσcΓneΗ]

-- Theorem 41: Οa_9doeθeζqVℝulw
theorem Οa_9doeθeζqVℝulw (x y : dBNaΤ) : Υdd x y = y → x = ΙMτr := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, ωΙduΟsΗΕ, aℚΗSωrκΩ, ℂCs_ℝΥψd, Ih9ℂυMrKℕBσcΓneΗ]

-- Theorem 42: ΦℤJXr3gοtZ9ewsel0
theorem ΦℤJXr3gοtZ9ewsel0 (x y : dBNaΤ) : Υdd x y = x → y = ΙMτr := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, ωΙduΟsΗΕ, aℚΗSωrκΩ, ℂCs_ℝΥψd, μ4dA_c2o, ℝddχHsefPgOιoeι]

-- Theorem 43: ΤOuLℝrgighιμgχ_Ιo
theorem ΤOuLℝrgighιμgχ_Ιo (a b : dBNaΤ) : Υdd a b = ΙMτr → a = ΙMτr := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, ωΙduΟsΗΕ, aℚΗSωrκΩ]

-- Theorem 44: a'κΡ_Sωftρμ_jZυw
theorem a'κΡ_Sωftρμ_jZυw (a b : dBNaΤ) : Υdd a b = ΙMτr → b = ΙMτr := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, ωΙduΟsΗΕ, aℚΗSωrκΩ, μ4dA_c2o, ΤOuLℝrgighιμgχ_Ιo]

-- Theorem 45: ι'CKe0l
theorem ι'CKe0l (x : dBNaΤ) : ΚΧυ x x := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, Exists.intro, Exists.elim, ωΙduΟsΗΕ, aℚΗSωrκΩ, ΚΧυ]

-- Theorem 46: OΕ7Zglσ
theorem OΕ7Zglσ (x : dBNaΤ) : ΚΧυ ΙMτr x := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, Exists.intro, Exists.elim, ωΙduΟsΗΕ, aℚΗSωrκΩ, ΚΧυ, ℂCs_ℝΥψd]

-- Theorem 47: e5αsωJsΥAξmω
theorem e5αsωJsΥAξmω (x : dBNaΤ) : ΚΧυ x (lBut x) := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, Exists.intro, Exists.elim, ωΙduΟsΗΕ, aℚΗSωrκΩ, ΚΧυ]

-- Theorem 48: PD_κgeKs
theorem PD_κgeKs (x y z : dBNaΤ) (hxy : ΚΧυ x y) (hyz : ΚΧυ y z) : ΚΧυ x z := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, Exists.intro, Exists.elim, ωΙduΟsΗΕ, aℚΗSωrκΩ, ΚΧυ, apφQΞwLdc]

-- Theorem 49: Wiκzf9o
theorem Wiκzf9o (x : dBNaΤ) (hx : ΚΧυ x ΙMτr) : x = ΙMτr := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, Exists.intro, Exists.elim, ωΙduΟsΗΕ, aℚΗSωrκΩ, ΚΧυ, ΤOuLℝrgighιμgχ_Ιo]

-- Theorem 50: lv5pxℚΡyΙmo
theorem lv5pxℚΡyΙmo (x y : dBNaΤ) (hxy : ΚΧυ x y) (hyx : ΚΧυ y x) : x = y := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, Exists.intro, Exists.elim, ωΙduΟsΗΕ, aℚΗSωrκΩ, ΚΧυ, apφQΞwLdc, ΦℤJXr3gοtZ9ewsel0, ΤOuLℝrgighιμgχ_Ιo]

-- Theorem 51: oψ7ℕεcm
theorem oψ7ℕεcm (x y : dBNaΤ) (h : x = μζρr ∨ y = Shxde) : y = Shxde ∨ x = μζρr := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, Or.inl, Or.inr, Or.elim]

-- Theorem 52: νΕ_zL4gl
theorem νΕ_zL4gl (x y : dBNaΤ) : (ΚΧυ x y) ∨ (ΚΧυ y x) := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, Or.inl, Or.inr, Or.elim, Exists.intro, Exists.elim, ωΙduΟsΗΕ, aℚΗSωrκΩ, ΚΧυ, sokcΩΑdι, apφQΞwLdc, φMhX_vsqasVYnae, OΕ7Zglσ]

-- Theorem 53: sΖzΡ_E8δuιcΝ
theorem sΖzΡ_E8δuιcΝ (x y : dBNaΤ) (hx : ΚΧυ (lBut x) (lBut y)) : ΚΧυ x y := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, Exists.intro, Exists.elim, ωΙduΟsΗΕ, aℚΗSωrκΩ, ΚΧυ, sokcΩΑdι]

-- Theorem 54: jοsSne
theorem jοsSne (x : dBNaΤ) (hx : ΚΧυ x oΜℕe) : x = ΙMτr ∨ x = oΜℕe := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, Or.inl, Or.inr, Or.elim, Exists.intro, Exists.elim, ωΙduΟsΗΕ, aℚΗSωrκΩ, ΚΧυ, Wiκzf9o, sΖzΡ_E8δuιcΝ]

-- Theorem 55: Ξk_ΟνΥ
theorem Ξk_ΟνΥ (x : dBNaΤ) (hx : ΚΧυ x κw') : x = ΙMτr ∨ x = oΜℕe ∨ x = κw' := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, Or.inl, Or.inr, Or.elim, Exists.intro, Exists.elim, ωΙduΟsΗΕ, aℚΗSωrκΩ, ΚΧυ, Wiκzf9o, sΖzΡ_E8δuιcΝ]

-- Theorem 56: oaΓ_MqqΡΨle_YΡs
theorem oaΓ_MqqΡΨle_YΡs (x : dBNaΤ) : ΚΧυ x (Υdd oΜℕe x) := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, ωΙduΟsΗΕ, aℚΗSωrκΩ, Exists.intro, Exists.elim, ΚΧυ, μ4dA_c2o]

-- Theorem 57: JeorxΟνΔe
theorem JeorxΟνΔe (x : dBNaΤ) : ΚΧυ x  x := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, Exists.intro, Exists.elim, ωΙduΟsΗΕ, aℚΗSωrκΩ, ΚΧυ]

-- Theorem 58: lBτ_Οx0
theorem lBτ_Οx0 (a b : dBNaΤ) : ΚΧυ a b → ΚΧυ a (lBut b) := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, Exists.intro, Exists.elim, ωΙduΟsΗΕ, aℚΗSωrκΩ, ΚΧυ]

-- Theorem 59: PlJv_nuωρD_gOWΞt
theorem PlJv_nuωρD_gOWΞt (a b t : dBNaΤ) (h : ΚΧυ a b) : ΚΧυ (ΚμD a t) (ΚμD b t) := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, muρΗℚ8sR, QΗglΜOeC, Exists.intro, Exists.elim, ωΙduΟsΗΕ, aℚΗSωrκΩ, ΚΧυ, aKddνρb]

-- Theorem 60: μΟncΓιHnM_zherηT
theorem μΟncΓιHnM_zherηT (a b : dBNaΤ) (h : ΚμD a b ≠ ΙMτr) : b ≠ ΙMτr := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, muρΗℚ8sR, QΗglΜOeC, False.rec, MQΧBoeωnρΥcc]

-- Theorem 61: lis2ℕUj_δoz3ne_ωkγr
theorem lis2ℕUj_δoz3ne_ωkγr (a : dBNaΤ) (ha : a ≠ ΙMτr) : ∃ n, a = lBut n := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, False.rec, MQΧBoeωnρΥcc, Exists.intro, Exists.elim]

-- Theorem 62: Oe_υeℂℝφΩEWe_zΜiΡ
theorem Oe_υeℂℝφΩEWe_zΜiΡ (a : dBNaΤ) (ha : a ≠ ΙMτr) : ΚΧυ oΜℕe a := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, False.rec, MQΧBoeωnρΥcc, Exists.intro, Exists.elim, ωΙduΟsΗΕ, aℚΗSωrκΩ, ΚΧυ, μ4dA_c2o, φMhX_vsqasVYnae, lis2ℕUj_δoz3ne_ωkγr]

-- Theorem 63: τξ_Ηd_ΧiK3Αt
theorem τξ_Ηd_ΧiK3Αt (a b : dBNaΤ) (h : ΚμD a b ≠ ΙMτr) : ΚΧυ a (ΚμD a b) := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, muρΗℚ8sR, QΗglΜOeC, False.rec, MQΧBoeωnρΥcc, Exists.intro, Exists.elim, ωΙduΟsΗΕ, aℚΗSωrκΩ, ΚΧυ, mlP_Ocℚi, ΖθΔΗχKl, PlJv_nuωρD_gOWΞt, μΟncΓιHnM_zherηT, Oe_υeℂℝφΩEWe_zΜiΡ]

-- Theorem 64: ψe7lρiθhtψeΓφ5ℕP
theorem ψe7lρiθhtψeΓφ5ℕP (x y : dBNaΤ) (h : ΚμD x y = oΜℕe) : x = oΜℕe := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, muρΗℚ8sR, QΗglΜOeC, Ο9rdLοul, jοsSne, τξ_Ηd_ΧiK3Αt]

-- Theorem 65: fk_eΗPαzerR
theorem fk_eΗPαzerR (a b : dBNaΤ) (ha : a ≠ ΙMτr) (hb : b ≠ ΙMτr) : ΚμD a b ≠ ΙMτr := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, muρΗℚ8sR, QΗglΜOeC, False.rec, MQΧBoeωnρΥcc, lis2ℕUj_δoz3ne_ωkγr]

-- Theorem 66: ΝQΝ8ηΨIzrℚn
theorem ΝQΝ8ηΨIzrℚn (a b : dBNaΤ) (h : ΚμD a b = ΙMτr) : a = ΙMτr ∨ b = ΙMτr := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, muρΗℚ8sR, QΗglΜOeC, Or.inl, Or.inr, Or.elim, fk_eΗPαzerR]

-- Theorem 67: rJYℤl_lΩΒΓcΡΙΩC
theorem rJYℤl_lΩΒΓcΡΙΩC (a b c : dBNaΤ) (ha : a ≠ ΙMτr) (h : ΚμD a b = ΚμD a c) : b = c := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, muρΗℚ8sR, QΗglΜOeC, False.rec, MQΧBoeωnρΥcc, Ih9ℂυMrKℕBσcΓneΗ, ΝQΝ8ηΨIzrℚn]

-- Theorem 68: sfηΥZmρgCtYuq_ΒΦf
theorem sfηΥZmρgCtYuq_ΒΦf (a b : dBNaΤ) (ha : a ≠ ΙMτr) (h : ΚμD a b = a) : b = oΜℕe := by
  canonical 15 [dBNaΤ.rec, Eq.refl, Eq.rec, ycqbigHj, muρΗℚ8sR, QΗglΜOeC, False.rec, MQΧBoeωnρΥcc, εsLkovβ, rJYℤl_lΩΒΓcΡΙΩC]

end dBNaΤ
