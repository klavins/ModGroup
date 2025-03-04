import Mathlib.Tactic
import ModGroup.Lib.Complex
import ModGroup.Lib.UHP
import ModGroup.Lib.SL2

open Complex

@[ext]
structure FLT where                        -- TODO: a general FLT class would
  a : ℤ                                    -- have any Ring as the type of of
  b : ℤ                                    -- a, b, c and d and would only
  c : ℤ                                    -- require a nonzero determinant.
  d : ℤ
  det1 : a*d - b*c = 1 := by decide

/- ## First Goal : FLT's preserve UHP

Our first goal is to define the map $z \mapsto (az+b)/(cz+d)$ and show it takes $z:UHP$ to $z:UHP$. A proof of this statement can be found [here](https://public.websites.umich.edu/~hlm/nzm/modgp.pdf). The proof is basically algebra, but there are a number of steps that a computer needs to understand before you can just crank through the equations.

To proceed, we need some helper theorems. This first one shows that if $z ≠ 0$ then the denominator $cz+d$ is also not equal to zero, which is required to even define the entire map. We will need this theorem in two different places in the ultimate proof. -/

theorem den_nz (f : FLT) (z: ℂ) : z.im ≠ 0 → f.c * z + f.d ≠ 0 := by

  match f with
  | ⟨ a,b,c,d, hdet ⟩ =>
  match z with
  | ⟨ x, y ⟩  =>

  intro hz h
  simp at h hz
  obtain ⟨ h1, h2 ⟩ := h

  cases h2

  case inl hc0 =>
    have hd : d = 0 := by simp_all[hc0]
    have : a * d - b * c = 0 := by simp[hc0,hd]
    simp[this] at hdet

  case inr hy0 => exact hz hy0

/- Now we define the map and include the associated proof that the map indeed goes from UHP to UHP.

***TODO***: Make this proof *much* simpler by factoring out more lemmas about Complex and UHP.

-/

noncomputable
def fl_map (f : FLT) (z : UHP) : UHP := ⟨ (f.a*z + f.b)/(f.c*z + f.d), by

    have hz  := den_nz f z (uhp_im_nz z)
    have hzc := den_nz f z.conj (uhp_conj_im_nz z)

    match f with
    | ⟨ a,b,c,d,hdet ⟩ =>
    match z with
    | ⟨ z, hpos ⟩ =>
    simp
    simp only [intCast_re, intCast_im,uhp_conj_simp] at hz hzc

    let q := (c * z.conj + d)

    have h1 : q ≠ 0 → q / q = 1 := by
      intro h
      field_simp

    have h2 : q ≠ 0 := by  exact hzc

    have h3 : q/q = 1 := h1 h2

    have h4 : (a * z + b)/(c * z + d)
            = (c*z.conj + d)*(a * z + b) / ((c*z.conj + d)*(c * z + d)) := by
      calc (a * z + b)/(c * z + d)
      _  = (a * z + b)/(c * z + d):= by simp
      _  = ((c*z.conj + d)/(c*z.conj + d))*(a * z + b)/(c * z + d) := by simp[h3,q]
      _  = (c*z.conj + d)*(a * z + b) / ((c*z.conj + d)*(c * z + d)) := by simp

    rw[h4,mul_by_conj_plus,split_helper]

    have h5 : (a:Complex)*d - b*c = 1 := by
      rw[lift_both_sides] at hdet
      simp at hdet
      exact hdet

    simp[h5]

    have hc0_to_d : c = 0 → d ≠ 0 := by
      intro hc0
      simp[hc0] at hdet
      exact right_ne_zero_of_mul_eq_one hdet

    have hznz : z.im ≠ 0 := by exact Ne.symm (ne_of_lt hpos)

    apply im_of_frac2
    . simp[im_of_sum]
      simp[im_zero_of_sq]
    . simp[re_of_sq]
      by_cases hc : c = 0
      . simp[hc]
        exact hc0_to_d hc
      . have h1 : ↑c * z.im * (↑c * z.im) > 0 := by
          simp[simp]
          exact ⟨ hc, λ hzi => by exact hznz hzi ⟩
        have h2 : (↑c * z.re + ↑d) * (↑c * z.re + ↑d) ≥ 0 := by
          exact mul_self_nonneg (↑c * z.re + ↑d)
        exact add_pos_of_nonneg_of_pos h2 h1
    . simp[im_of_sum]
      simp[z_norm_im_zero]
      exact hpos

⟩

/- Here is an example showing the use of the map. Note that it would throw a type error if the output of fl_map were not in UHP. So this short statement actually packs a lot of information into it. -/

/- ## FLT is a group

Now we can start proving FLT is a group!

 -/

noncomputable
instance fl_coe_fun: CoeFun FLT (λ _ => UHP → UHP) :=
  ⟨ λ f => (λ z => fl_map f z) ⟩

def fl_to_sl2 (f : FLT) : SL2
  := ⟨ !![f.a,f.b;f.c,f.d], by simp[f.det1] ⟩

def sl2_to_fl (A : SL2) : FLT
  := ⟨ A 0 0, A 0 1, A 1 0, A 1 1, by
    have h := A.det1
    simp[Matrix.det_fin_two] at h
    exact h⟩

theorem sl2_map_map : sl2_to_fl ∘ fl_to_sl2 = id := by
  funext
  simp[fl_to_sl2,sl2_to_fl]

theorem fl_map_map : fl_to_sl2 ∘ sl2_to_fl = id := by
  funext A
  simp[fl_to_sl2,sl2_to_fl,SL2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem sl2_eq_imp_fl_eq (f g : FLT): fl_to_sl2 f = fl_to_sl2 g → f = g := by
  intro h
  simp[fl_to_sl2] at h
  apply Matrix.ext_iff.mpr at h
  ext
  . apply h 0 0
  . apply h 0 1
  . apply h 1 0
  . apply h 1 1

theorem fl_eq_imp_sl2_eq (f g : FLT): f = g → fl_to_sl2 f = fl_to_sl2 g := by
  intro hfg
  apply FLT.ext_iff.mp at hfg
  obtain ⟨ ha, hb, hc, hd ⟩ := hfg
  simp[fl_to_sl2,ha,hb,hc,hd]

def fl_comp (f g : FLT) : FLT := -- TODO: CHECK THIS!!!
  let A := fl_to_sl2 f
  let B := fl_to_sl2 g
  let AB := A*B
  ⟨ AB 0 0, AB 0 1, AB 1 0, AB 1 1, by
    have h := AB.det1
    simp[Matrix.det_fin_two] at h
    exact h ⟩

theorem cancel_dens {a b c d x y : ℂ}
  : y ≠ 0 → (a*(x/y) + b*y/y)/(c*(x/y)+d*y/y) = (a*x+b*y)/(c*x+d*y):= by
  intro h
  field_simp

/- Check that fl_comp as defined above with matrix multiplication is equivalen to actual function composition. -/
example (f g: FLT): fl_comp f g = f ∘ g := by

  simp[fl_comp,fl_map,fl_to_sl2]
  funext x
  simp

  have hf := den_nz f x (uhp_im_nz x)
  have hg := den_nz g x (uhp_im_nz x)

  have : (↑g.c * x.z + ↑g.d) / (↑g.c * x.z + ↑g.d) = 1 := by
    apply div_self; exact hg

  have hfb : f.b = f.b * (↑g.c * x.z + ↑g.d) / (↑g.c * x.z + ↑g.d) := by
    exact Eq.symm (mul_div_cancel_right₀ (↑f.b) hg)

  have hfd : f.d = f.d * (↑g.c * x.z + ↑g.d) / (↑g.c * x.z + ↑g.d) := by
    exact Eq.symm (mul_div_cancel_right₀ (↑f.d) hg)

  conv =>
    rhs
    rw[hfb,hfd]

  conv =>
    rhs
    rw[cancel_dens hg]

  ring

noncomputable
def fl_inv (f : FLT) : FLT :=
  sl2_to_fl ( (fl_to_sl2 f)⁻¹)

instance fl_inhabited : Inhabited FLT := ⟨ ⟨ 1,0,0,1,rfl ⟩ ⟩

instance fl_hmul_inst : HMul FLT FLT FLT := ⟨ fl_comp ⟩

instance fl_mul_inst : Mul FLT := ⟨ fl_comp ⟩

noncomputable
instance fl_inv_inst : Inv FLT := ⟨ fl_inv ⟩

def fl_one : FLT := ⟨ 1, 0, 0, 1, rfl ⟩

instance fl_one_inst : One FLT := ⟨ fl_one ⟩

theorem fl_comp_sl2 (f g : FLT)
  : fl_to_sl2 (f*g) = (fl_to_sl2 f) * (fl_to_sl2 g) := by
    simp[fl_to_sl2,fl_hmul_inst,fl_comp]

theorem fl_comp_sl2_iff (f g h: FLT)
  : h = f * g ↔ (fl_to_sl2 h) = (fl_to_sl2 f) * (fl_to_sl2 g) := by
  apply Iff.intro
  . intro h1
    simp_all[fl_to_sl2,fl_hmul_inst,fl_comp]
  . intro h2
    rw[←fl_comp_sl2] at h2
    apply sl2_eq_imp_fl_eq at h2
    exact h2

theorem fl_mul_assoc : ∀ f g h : FLT, f * g * h = f * (g * h) := by
  intro f g h
  simp[fl_comp_sl2_iff,fl_to_sl2,fl_hmul_inst,fl_comp]
  exact ⟨ by ring, by ring, by ring, by ring ⟩

instance fl_semi_inst: Semigroup FLT :=
  ⟨ fl_mul_assoc ⟩

theorem fl_mul_one_left (f : FLT) : 1 * f = f := by
  have : 1 = fl_one := rfl
  rw[this]
  simp[fl_hmul_inst,fl_to_sl2,fl_comp,fl_one]

theorem fl_mul_one_right (f : FLT) : f * 1= f := by
  have : 1 = fl_one := rfl
  rw[this]
  simp[fl_hmul_inst,fl_to_sl2,fl_comp,fl_one]

instance fl_mul_one_inst : MulOneClass FLT :=
  ⟨ fl_mul_one_left, fl_mul_one_right ⟩

def fl_adj (f : FLT) : FLT := ⟨ f.d, -f.b, -f.c, f.a, by
  have h := f.det1
  rw[←h]
  ring
 ⟩

theorem fl_inv_adj (f : FLT) : f⁻¹ = fl_adj f := by
  simp[fl_inv_inst,fl_inv,sl2_to_fl,fl_to_sl2]
  simp[Matrix.inv]
  simp[f.det1,fl_adj]

theorem fl_inv_left : ∀ f : FLT, f⁻¹ * f = 1 := by
  intro f
  rw[fl_inv_adj]
  have : 1 = fl_one := rfl
  rw[this]
  simp[fl_hmul_inst,fl_comp,fl_adj,fl_to_sl2,fl_one]
  have h := f.det1
  rw[←h]
  exact ⟨ by ring, by ring, by ring, by ring ⟩

theorem fl_inv_right : ∀ f : FLT, f * f⁻¹ = 1 := by
  intro f
  rw[fl_inv_adj]
  have : 1 = fl_one := rfl
  rw[this]
  simp[fl_hmul_inst,fl_comp,fl_adj,fl_to_sl2,fl_one]
  have h := f.det1
  rw[←h]
  exact ⟨ by ring, by ring, by ring, by ring ⟩

noncomputable
instance fl_group_inst : Group FLT :=
  @Group.ofLeftAxioms FLT _ _ _ fl_mul_assoc fl_mul_one_left fl_inv_left
