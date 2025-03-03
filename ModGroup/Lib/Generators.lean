/- This will eventually contain the solution to exercies 1.1.1 of [Diamond and Shurman](https://public.websites.umich.edu/~hlm/nzm/modgp.pdf). -/

import ModGroup.Lib.SL2

/- Generators of SL2 -/
def T := SL2.mk !![1,1;0,1]
def S := SL2.mk !![0, -1; 1, 0]

/- Simplified version of T^n-/
def Tpow (n:ℕ) : SL2 := ⟨ !![1,n;0,1], by simp ⟩

/- Useful intermediate matrix -/
def MTpow (M : Matrix (Fin 2) (Fin 2) ℤ) (n:ℕ) : Matrix (Fin 2) (Fin 2) ℤ  :=
  !![ M 0 0, (M 0 0)*n + M 0 1;
      M 1 0, (M 1 0)*n + M 1 1 ]

/- T^n : SL2 -/
theorem Tn {n:ℕ} : T^n = Tpow n := by
  unfold Tpow
  induction n with
  | zero => simp; exact Matrix.one_fin_two
  | succ k ih =>
    have : T^(k+1) = T^k * T := rfl
    rw[this,ih,T]
    simp[add_comm]

theorem Tn_val {n:ℕ} : T.val^n = Tpow n := by
  unfold Tpow
  induction n with
  | zero => simp; exact Matrix.one_fin_two
  | succ k ih =>
    have : T.val^(k+1) = T.val^k * T.val := rfl
    rw[this,ih,T]
    simp[add_comm]

/- Helpful Identity -/
theorem mt_pow {M : Matrix (Fin 2) (Fin 2) ℤ} {n:ℕ} : M * T^n = MTpow M n := by
    unfold MTpow
    rw[Tn_val,Tpow,Matrix.eta_fin_two M]
    simp

/- Show that unless c = 0, some matrix αγ with γ ∈ Γ has bottom row (c, d′) with |d′| ≤ |c|/2. -/
theorem alpha_gamma (c:ℚ)
  : c > 0 → ∃ α : Matrix (Fin 2) (Fin 2) ℤ ,
            ∃ γ : SL2, (α*γ) 1 0 = c ∧ |(α*γ) 1 1| ≤ |c|/2 := by
  intro hc
  sorry
