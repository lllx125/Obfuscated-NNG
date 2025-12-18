import Mathlib.Tactic.ApplyAt
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Use
import Mathlib.Tactic.Tauto

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

theorem ℂCs_ℝΥψd (n : dBNaΤ) : Υdd ΙMτr n = n := by
  sorry

theorem sokcΩΑdι (a b : dBNaΤ) : Υdd (lBut a) b = lBut (Υdd a b)  := by
  sorry

theorem μ4dA_c2o (a b : dBNaΤ) : Υdd a b = Υdd b a := by
  sorry

theorem apφQΞwLdc (a b c : dBNaΤ) : Υdd (Υdd a b) c = Υdd a (Υdd b c) := by
  sorry

theorem aΨ_rνykn8ΨcρΥT (a b c : dBNaΤ) : Υdd (Υdd a b) c = Υdd (Υdd a c) b := by
  sorry

theorem ΥdΝefetkℂcCηg (a b c : dBNaΤ) : Υdd a (Υdd b c) = Υdd b (Υdd a c) := by
  sorry

theorem φMhX_vsqasVYnae (n : dBNaΤ) : lBut n = Υdd n oΜℕe := by
  sorry

theorem Ξbα9PhiΔcaHκ_nκ (x y z : dBNaΤ) (h1 : Υdd x y = μζρr) (h2 : Υdd (ΚμD Shxde x) z = κw') : Υdd x y = μζρr := by
  sorry

theorem icplXRapGoHXRho (x y : dBNaΤ) (h : Υdd ΙMτr x = Υdd (Υdd ΙMτr y) κw') : x = Υdd y κw' := by
  sorry

theorem GΜvpΝiΝahqonV0Δre (x y : dBNaΤ) (h1 : x = Shxde) (h2 : x = Shxde → y = μζρr) : y = μζρr := by
  sorry

theorem HζΕιχ9ΝonξfxΡuΒr (x : dBNaΤ) (h : Υdd x oΜℕe = μζρr) : x = Shxde := by
  sorry

theorem I5WXliAΚdnℂRfiΤvq (x : dBNaΤ) : x = μζρr → x = μζρr := by
  sorry

theorem ξπ4piΦaμoβG3sΧΙ (x y : dBNaΤ) : Υdd x oΜℕe = Υdd y oΜℕe → x = y := by
  sorry

theorem υΟmmplΔΥuωβΞnysue (x y : dBNaΤ) (h1 : x = y) (h2 : x ≠ y) : False := by
  sorry

theorem V5_XMexℤoΥΘe : (ΙMτr : dBNaΤ) ≠ oΜℕe := by
  sorry

theorem onByxTzte5γ : (oΜℕe : dBNaΤ) ≠ ΙMτr := by
  sorry

theorem t8tpKuφ_wt'ΝφNe9Βvoe : Υdd (lBut (lBut ΙMτr)) (lBut (lBut ΙMτr)) ≠ lBut (lBut (lBut (lBut (lBut ΙMτr)))) := by
  sorry

theorem υ2_εlKγ351 (a b c d : dBNaΤ) : Υdd (Υdd a b) (Υdd c d) = Υdd (Υdd (Υdd a c) d) b := by
  sorry

theorem Εcyc_9ΦΩΝσZo (a : dBNaΤ) : lBut a ≠ ΙMτr := by
  sorry

theorem GnℂΩμne_φΗ6N (m n : dBNaΤ) (h : m ≠ n) : lBut m ≠ lBut n := by
  sorry

theorem εsLkovβ (m : dBNaΤ) : ΚμD m oΜℕe = m := by
  sorry

theorem Ο9rdLοul (m : dBNaΤ) : ΚμD ΙMτr m = ΙMτr := by
  sorry

theorem NΑℕ_ψmuΔ (a b : dBNaΤ) : ΚμD (lBut a) b = Υdd (ΚμD a b) b := by
  sorry

theorem mlP_Ocℚi (a b : dBNaΤ) : ΚμD a b = ΚμD b a := by
  sorry

theorem ΖθΔΗχKl (m : dBNaΤ) : ΚμD oΜℕe m = m := by
  sorry

theorem tkμΚΜWν (m : dBNaΤ) : ΚμD κw' m = Υdd m m := by
  sorry

theorem ApΝℕιaΑ (a b c : dBNaΤ) : ΚμD a (Υdd b c) = Υdd (ΚμD a b) (ΚμD a c) := by
  sorry

theorem aKddνρb (a b c : dBNaΤ) : ΚμD (Υdd a b) c = Υdd (ΚμD a c) (ΚμD b c) := by
  sorry

theorem H1πlZsℕxΥc (a b c : dBNaΤ) : ΚμD (ΚμD a b) c = ΚμD a (ΚμD b c)  := by
  sorry

theorem zℕ_ozΝDzHKΒσo : Γoq (ΙMτr : dBNaΤ)  ΙMτr = oΜℕe := by
  sorry

theorem σwro_pℝπts1vv (m : dBNaΤ) : Γoq (ΙMτr : dBNaΤ) (lBut m) = ΙMτr := by
  sorry

theorem zJDvnΗe (a : dBNaΤ) : Γoq a oΜℕe = a  := by
  sorry

theorem ΙγnεμBw (m : dBNaΤ) : Γoq (oΜℕe : dBNaΤ) m = oΜℕe := by
  sorry

theorem ηFw_ΓJκ (a : dBNaΤ) : Γoq a κw' = ΚμD a a := by
  sorry

theorem ραΩ4aAd (a m n : dBNaΤ) : Γoq a (Υdd m n) = ΚμD (Γoq a m) (Γoq a n) := by
  sorry

theorem o25pxΨw (a b n : dBNaΤ) : Γoq (ΚμD a b) n = ΚμD (Γoq a n) (Γoq b n) := by
  sorry

theorem οJi_ZΙw (a m n : dBNaΤ) : Γoq (Γoq a m) n = Γoq a (ΚμD m n) := by
  sorry

theorem axysSρ (a b : dBNaΤ) : Γoq (Υdd a b) κw' = Υdd (Υdd (Γoq a κw') (Γoq b κw')) (ΚμD (ΚμD κw' a) b) := by
  sorry

theorem Ih9ℂυMrKℕBσcΓneΗ (a b n : dBNaΤ) : Υdd a n = Υdd b n → a = b := by
  sorry

theorem ℝddχHsefPgOιoeι (a b n : dBNaΤ) : Υdd n a = Υdd n b → a = b := by
  sorry

theorem Οa_9doeθeζqVℝulw (x y : dBNaΤ) : Υdd x y = y → x = ΙMτr := by
theorem Οa_9doeθeζqVℝulw (x y : dBNaΤ) : x + y = y → x = Ζινr := by
  intro h
  induction y with
  | Ζινr =>
      rw [aℚΗSωrκΩ] at h
      exact h
  | a'gχc d ih =>
      rw [ωΙduΟsΗΕ] at h
      have h2 : x + d = d := ΒΝη_RFnδ (x + d) d h
      exact ih x h2

theorem ΦℤJXr3gοtZ9ewsel0 (x y : dBNaΤ) : Υdd x y = x → y = ΙMτr := by
theorem ΦℤJXr3gοtZ9ewsel0 (x y : dBNaΤ) : x + y = x → y = Ζινr := by
  intro h
  rw [μ4dA_c2o] at h
  exact Οa_9doeθeζqVℝulw y x h

theorem ΤOuLℝrgighιμgχ_Ιo (a b : dBNaΤ) : Υdd a b = ΙMτr → a = ΙMτr := by
theorem ΤOuLℝrgighιμgχ_Ιo (a b : dBNaΤ) : a + b = Ζινr → a = Ζινr := by
  intro h
  cases a with
  | Ζινr =>
      rfl
  | a'gχc a0 =>
      rw [LcDTV5d1] at h
      exfalso
      exact (ΞQℝℂrxΥ9e_βc (a0 + b)) (Eq.symm h)

theorem a'κΡ_Sωftρμ_jZυw (a b : dBNaΤ) : Υdd a b = ΙMτr → b = ΙMτr := by
theorem a'κΡ_Sωftρμ_jZυw (a b : dBNaΤ) : a + b = Ζινr → b = Ζινr := by
  intro h
  rw [μ4dA_c2o] at h
  exact ΤOuLℝrgighιμgχ_Ιo b a h

theorem ι'CKe0l (x : dBNaΤ) : ΚΧυ x x := by
theorem lBqBθγΤ (x : dBNaΤ) : x ≤ x := by
  exact ⟨Ζινr, (aℚΗSωrκΩ x).symm⟩

theorem OΕ7Zglσ (x : dBNaΤ) : ΚΧυ ΙMτr x := by
theorem keFΩmCv (x : dBNaΤ) : Ζινr ≤ x := by
  exact ⟨x, (ℝ5QrγΞMa x).symm⟩

theorem e5αsωJsΥAξmω (x : dBNaΤ) : ΚΧυ x (lBut x) := by
theorem B9e_fqΜΕ_ΨlκZ (x : dBNaΤ) : x ≤ a'gχc x := by
  use one
  exact ΩuWΒcℚoqe_θd_lZ x

theorem PD_κgeKs (x y z : dBNaΤ) (hxy : ΚΧυ x y) (hyz : ΚΧυ y z) : ΚΧυ x z := by
theorem lbw_iBqs (x y z : dBNaΤ) (hxy : x ≤ y) (hyz : y ≤ z) : x ≤ z := by
  cases hxy with
  | intro c h1 =>
    cases hyz with
    | intro d h2 =>
        use c + d
        rw [h2, h1, apφQΞwLdc]

theorem Wiκzf9o (x : dBNaΤ) (hx : ΚΧυ x ΙMτr) : x = ΙMτr := by
theorem ωπqαzeΖ (x : dBNaΤ) (hx : x ≤ Ζινr) : x = Ζινr := by
  cases hx with
  | intro c h =>
      apply ΤOuLℝrgighιμgχ_Ιo x c
      symm
      exact h

theorem lv5pxℚΡyΙmo (x y : dBNaΤ) (hxy : ΚΧυ x y) (hyx : ΚΧυ y x) : x = y := by
theorem ο1οCaILi9ym (x y : dBNaΤ) (hxy : x ≤ y) (hyx : y ≤ x) : x = y := by
  rcases hxy with ⟨c1, hc1⟩
  rcases hyx with ⟨c2, hc2⟩
  have h : y = y + (c2 + c1) :=
    calc
      y = x + c1 := hc1
      _ = (y + c2) + c1 := by rw [hc2]
      _ = y + (c2 + c1) := by rw [apφQΞwLdc]
  have h' : c2 + c1 = Ζινr := by
    apply ΦℤJXr3gοtZ9ewsel0 y (c2 + c1)
    exact Eq.symm h
  have hc2_zero : c2 = Ζινr := by
    apply ΤOuLℝrgighιμgχ_Ιo c2 c1 h'
  rw [hc2_zero] at hc2
  rw [aℚΗSωrκΩ] at hc2
  exact hc2

theorem oψ7ℕεcm (x y : dBNaΤ) (h : x = μζρr ∨ y = Shxde) : y = Shxde ∨ x = μζρr := by
theorem r_ΖrΥηK (x y : dBNaΤ) (h : x = μζρr ∨ y = υqGee) : y = υqGee ∨ x = μζρr := by
  cases h with
  | inl hx => right; exact hx
  | inr hy => left; exact hy

theorem νΕ_zL4gl (x y : dBNaΤ) : (ΚΧυ x y) ∨ (ΚΧυ y x) := by
theorem lVδℝFozJ (x y : dBNaΤ) : x ≤ y ∨ y ≤ x := by
  induction x with
  | Ζινr =>
      left
      exact keFΩmCv y
  | a'gχc x' ih =>
      induction y with
      | Ζινr =>
          right
          exact keFΩmCv (a'gχc x')
      | a'gχc y' =>
          rcases ih y' with (h | h)
          · left
            rcases h with ⟨c, hc⟩
            use c
            rw [LcDTV5d1, hc]
          · right
            rcases h with ⟨c, hc⟩
            use c
            rw [LcDTV5d1, hc]

theorem sΖzΡ_E8δuιcΝ (x y : dBNaΤ) (hx : ΚΧυ (lBut x) (lBut y)) : ΚΧυ x y := by
theorem ufcodηehℕuΜl (x y : dBNaΤ) (hx : a'gχc x ≤ a'gχc y) : x ≤ y := by
  cases hx with
  | intro c h =>
      rw [LcDTV5d1 x c] at h
      use c
      exact ΒΝη_RFnδ y (x + c) h

theorem jοsSne (x : dBNaΤ) (hx : ΚΧυ x oΜℕe) : x = ΙMτr ∨ x = oΜℕe := by
theorem lΧπΩWδ (x : dBNaΤ) (hx : x ≤ one) : x = Ζινr ∨ x = one := by
  cases x with
  | Ζινr =>
    left
    rfl
  | a'gχc y =>
    right
    rcases hx with ⟨c, hc⟩
    rw [oγn2T_ρ_s1'uzPXΑ] at hc
    rw [LcDTV5d1] at hc
    have h_eq := ΒΝη_RFnδ Ζινr (y + c) hc
    have h_sum : y + c = Ζινr := Eq.symm h_eq
    have hy := ΤOuLℝrgighιμgχ_Ιo y c h_sum
    rw [hy]
    rfl

theorem Ξk_ΟνΥ (x : dBNaΤ) (hx : ΚΧυ x κw') : x = ΙMτr ∨ x = oΜℕe ∨ x = κw' := by
theorem eΖpο9o (x : dBNaΤ) (hx : x ≤ two) : x = Ζινr ∨ x = one ∨ x = two := by
  cases x with
  | Ζινr =>
    left
    rfl
  | a'gχc n =>
    rw [ΥQnΧqaΖcZcIξoΙM] at hx
    have hle : n ≤ one := ufcodηehℕuΜl n one hx
    cases (lΧπΩWδ n hle) with
    | inl hn =>
      right
      left
      rw [hn]
      rfl
    | inr hn =>
      right
      right
      rw [hn]
      rfl

theorem oaΓ_MqqΡΨle_YΡs (x : dBNaΤ) : ΚΧυ x (Υdd oΜℕe x) := by
theorem ΗH0aOυlDφΩ6eΒlf (x : dBNaΤ) : x ≤ one + x := by
  rw [μ4dA_c2o, ΩuWΒcℚoqe_θd_lZ]
  exact B9e_fqΜΕ_ΨlκZ x

theorem JeorxΟνΔe (x : dBNaΤ) : ΚΧυ x  x := by
theorem MΝlj0iζ7e (x : dBNaΤ) : x ≤ x := by
  exact lBqBθγΤ x

theorem lBτ_Οx0 (a b : dBNaΤ) : ΚΧυ a b → ΚΧυ a (lBut b) := by
theorem xe'ℕVτc (a b : dBNaΤ) : a ≤ b → a ≤ (a'gχc b) := by
  intro h
  cases h with
  | intro c h_eq =>
      use a'gχc c
      rw [h_eq, ← ωΙduΟsΗΕ]

theorem PlJv_nuωρD_gOWΞt (a b t : dBNaΤ) (h : ΚΧυ a b) : ΚΧυ (ΚμD a t) (ΚμD b t) := by
theorem Tuμ_bfrΙmΖ3gigTt (a b t : dBNaΤ) (h : a ≤ b) : a * t ≤ b * t := by
  cases h with
  | intro c hc =>
    use c * t
    rw [hc, aKddνρb]

theorem μΟncΓιHnM_zherηT (a b : dBNaΤ) (h : ΚμD a b ≠ ΙMτr) : b ≠ ΙMτr := by
theorem NmhΨlKlpβtS0XCΒo (a b : dBNaΤ) (h : a * b ≠ Ζινr) : b ≠ Ζινr := by
  intro hb
  have H : a * b = Ζινr := by
    rw [hb]
    exact mℚΜlψΗξΘ a
  exact h H

theorem lis2ℕUj_δoz3ne_ωkγr (a : dBNaΤ) (ha : a ≠ ΙMτr) : ∃ n, a = lBut n := by
theorem lis2ℕUj_δoz3ne_ωkγr (a : dBNaΤ) (ha : a ≠ Ζινr) : ∃ n, a = a'gχc n := by
  cases a with
  | Ζινr => exact False.elim (ha rfl)
  | a'gχc n => exact ⟨n, rfl⟩

theorem Oe_υeℂℝφΩEWe_zΜiΡ (a : dBNaΤ) (ha : a ≠ ΙMτr) : ΚΧυ oΜℕe a := by
theorem wΔn'WΟejBΙnΔ_9eIΒ (a : dBNaΤ) (ha : a ≠ Ζινr) : one ≤ a := by
  have h : ∃ n, a = a'gχc n := lis2ℕUj_δoz3ne_ωkγr a ha
  rcases h with ⟨n, hn⟩
  rw [hn]
  use n
  rw [ΩuWΒcℚoqe_θd_lZ, μ4dA_c2o]

theorem τξ_Ηd_ΧiK3Αt (a b : dBNaΤ) (h : ΚμD a b ≠ ΙMτr) : ΚΧυ a (ΚμD a b) := by
theorem levmΚψ1tuSΤt (a b : dBNaΤ) (h : a * b ≠ Ζινr) : a ≤ a * b := by
  have hb : b ≠ Ζινr := NmhΨlKlpβtS0XCΒo a b h
  cases (lis2ℕUj_δoz3ne_ωkγr b hb) with
  | intro b0 hb0 =>
      rw [ΗeCGΟIΚοstsω_τaιw]
      use a * b0
      rw [hb0, E6uOΕu8χc, μ4dA_c2o]

theorem ψe7lρiθhtψeΓφ5ℕP (x y : dBNaΤ) (h : ΚμD x y = oΜℕe) : x = oΜℕe := by
theorem ΞuD_rgh30fgCqsσΘ (x y : dBNaΤ) (h : x * y = one) : x = one := by
  have h_one_ne : one ≠ Ζινr := by
    have h0 : Ζινr ≠ one := ΞQℝℂrxΥ9e_βc Ζινr
    intro h_eq
    apply h0
    rw [h_eq]
  have hne_prod : x * y ≠ Ζινr := by
    rw [h]
    exact h_one_ne
  have hx_le : x ≤ one := by
    have h1 : x ≤ x * y := levmΚψ1tuSΤt x y hne_prod
    rw [h] at h1
    exact h1
  have hx_ne : x ≠ Ζινr := by
    have h_comm : x * y = y * x := muΤc5jmO x y
    have hne_prod' : y * x ≠ Ζινr := by
      rw [← h_comm]
      exact hne_prod
    exact NmhΨlKlpβtS0XCΒo y x hne_prod'
  have h_one_le_x : one ≤ x := wΔn'WΟejBΙnΔ_9eIΒ x hx_ne
  exact ο1οCaILi9ym x one hx_le h_one_le_x

theorem fk_eΗPαzerR (a b : dBNaΤ) (ha : a ≠ ΙMτr) (hb : b ≠ ΙMτr) : ΚμD a b ≠ ΙMτr := by
theorem mH_Ξ9yzΨΩrh (a b : dBNaΤ) (ha : a ≠ Ζινr) (hb : b ≠ Ζινr) : a * b ≠ Ζινr := by
  intro h
  cases lis2ℕUj_δoz3ne_ωkγr a ha with
  | intro a0 ha0 =>
      rw [ha0] at h
      rw [u3zΟKsKΩ] at h
      have h2 : b = Ζινr := a'κΡ_Sωftρμ_jZυw (a0 * b) b h
      contradiction

theorem ΝQΝ8ηΨIzrℚn (a b : dBNaΤ) (h : ΚμD a b = ΙMτr) : a = ΙMτr ∨ b = ΙMτr := by
theorem mNπlΥΖxzνDo (a b : dBNaΤ) (h : a * b = Ζινr) : a = Ζινr ∨ b = Ζινr := by
  cases a with
  | Ζινr =>
    left
    rfl
  | a'gχc a' =>
    cases b with
    | Ζινr =>
      right
      rfl
    | a'gχc b' =>
      have h1 : a'gχc a' ≠ Ζινr := by
        intro h2
        apply ΞQℝℂrxΥ9e_βc a'
        symm
        exact h2
      have h2 : a'gχc b' ≠ Ζινr := by
        intro h3
        apply ΞQℝℂrxΥ9e_βc b'
        symm
        exact h3
      have h3 : (a'gχc a') * (a'gχc b') ≠ Ζινr := mH_Ξ9yzΨΩrh (a'gχc a') (a'gχc b') h1 h2
      contradiction

theorem rJYℤl_lΩΒΓcΡΙΩC (a b c : dBNaΤ) (ha : a ≠ ΙMτr) (h : ΚμD a b = ΚμD a c) : b = c := by
theorem LΜlxeεΖcξcBτHcκ (a b c : dBNaΤ) (ha : a ≠ Ζινr) (h : a * b = a * c) : b = c := by
  have h_order := lVδℝFozJ b c
  cases h_order with
  | inl hbc =>
      cases hbc with
      | intro d hd =>
          rw [hd] at h
          rw [gnwψ_Ηd] at h
          symm at h
          have hd_zero : a * d = Ζινr := ΦℤJXr3gοtZ9ewsel0 (a * b) (a * d) h
          cases mNπlΥΖxzνDo a d hd_zero with
          | inl ha' => contradiction
          | inr hd' =>
              rw [hd'] at hd
              rw [aℚΗSωrκΩ] at hd
              exact hd.symm
  | inr hcb =>
      cases hcb with
      | intro d hd =>
          rw [hd] at h
          rw [gnwψ_Ηd] at h
          symm at h
          have hd_zero : a * d = Ζινr := ΦℤJXr3gοtZ9ewsel0 (a * c) (a * d) h
          cases mNπlΥΖxzνDo a d hd_zero with
          | inl ha' => contradiction
          | inr hd' =>
              rw [hd'] at hd
              rw [aℚΗSωrκΩ] at hd
              exact hd

theorem sfηΥZmρgCtYuq_ΒΦf (a b : dBNaΤ) (ha : a ≠ ΙMτr) (h : ΚμD a b = a) : b = oΜℕe := by
theorem uMκq1qΡYtΡδeP_sGf (a b : dBNaΤ) (ha : a ≠ Ζινr) (h : a * b = a) : b = one := by
  apply LΜlxeεΖcξcBτHcκ a b one ha
  rw [RYuloqℤ]
  exact h

end dBNaΤ
