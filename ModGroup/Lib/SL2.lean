import Mathlib.Tactic
import Mathlib.Algebra.Group.MinimalAxioms

@[ext]
structure SL2 where
  val : Matrix (Fin 2) (Fin 2) ℤ
  det1 : val.det = 1 := by decide

/- To get started, we can show that SL2 is inhabited by assigned a default element, in this case, the identity matrix. -/

instance mod_inhabited_inst : Inhabited SL2 := ⟨ SL2.mk !![1,0;0,1] ⟩

def SL2.default : SL2 := Inhabited.default

/- ## Classes and Instances

We would like to use all the notation and theorems associated with groups without reproving everything. To that end, we will use the following classes:

| Class | Meaning |
| --- | --- |
| `Inhabited`   | SL2 has at least one element |
| `CoeSort`     | Write A instead of A.val when context is clear |
| `HMul`, `Mul` | SL2 has multiplication |
| `Inv`         | SL2 has inverses |
| `One`         | SL2 has an identity |
| `SemiGroup`   | SL2 multiplication is associative |
| `MulOneClass` | $1A = A$ |
| `Group`       | $A⁻¹A = 1$ and $AA⁻¹ = 1$ |

-/

/- ## Coercion

When we have M : SL2, we would like use M as a matrix. But we end up having to write M.val in such contexts. For example, in the first attempt at definition multiplicaton below, the first argument to the constructor expects a matrix. In the second, we use the matrix as a function. -/

/- To make our code more readable, we can provide a coercion from SL2 into a Matrix or a function. -/

instance mod_group_coe: CoeSort SL2 (Matrix (Fin 2) (Fin 2) ℤ) :=
  ⟨ λ M => M.val ⟩

instance mod_group_coe_fun: CoeFun SL2 (λ _ => (Fin 2) → (Fin 2) → ℤ) :=
  ⟨ λ M => (λ i j => M.val i j) ⟩

/- Now the above definition can be written concisely. -/
def sl2_mul (A B : SL2) : SL2 := ⟨ A * B, by simp[A.det1,B.det1] ⟩

instance sl2_hmul_inst: HMul SL2 SL2 SL2 :=
  ⟨ sl2_mul ⟩

instance sl2_mul_inst: Mul SL2 :=
  ⟨ sl2_mul ⟩

/- It is also quite useful to tell the simplifier what multiplication means, so that you don't have to constantly be breaking this definition down inside proofs. -/

@[simp]
theorem sl2_mul_simp (A B : SL2) : A * B = ⟨ A*B, by simp[A.det1,B.det1] ⟩ := by
  calc A * B
  _  = ⟨ A, A.det1 ⟩ * ⟨ B, B.det1 ⟩ := rfl
  _  = ⟨ A*B, by simp[A.det1,B.det1] ⟩ := rfl --!hide

/- ## Inverses

Next we show that the inverse of every element of type SL2 is also of type SL2. This is because the determinant of the inverse of a matrix is the inverse of its determinant, and SL2 determinants are all 1. -/

noncomputable                             -- noncomputable because this method does
instance sl2_inv_inst: Inv SL2 :=         -- not show how to derive the inverse, just
  ⟨ λ M => ⟨ M⁻¹, by simp[M.det1] ⟩  ⟩    -- that it exists since M.det = 1.

@[simp]
theorem sl2_inv_simp (A : SL2) : A⁻¹ = ⟨ A⁻¹, by simp[A.det1] ⟩ := rfl

/- Recall that the inverse of a matrix $A$ , when it exists, is $|A|^{-1}$ times the adjunct of $A$. Since SL2 determinants are all 1, we can show that the inverse of a matrix of type SL2 is equal to its adjunct.

First we define the adjunct of a matrix. -/

def adj (A : SL2) : SL2 := ⟨ !![A 1 1, -A 0 1; -A 1 0, A 0 0 ], by
  dsimp
  have h := A.det1
  simp_all[Matrix.det_fin_two]
  rw[←h]
  ring ⟩

/- Then we state and prove our first theorem. -/

theorem sl2_inv_simp_eq_adj (A : SL2) : A⁻¹ = adj A := by
  simp[adj,sl2_inv_inst]
  simp[Matrix.inv]
  have h : A.val.det = 1 := by apply A.det1
  simp[h]
  simp[Matrix.adjugate_fin_two]


@[simp]
def one : SL2 := ⟨ 1, by simp ⟩

instance sl2_one_inst: One SL2 := ⟨ one ⟩

/- It also helps to explain to the simplifier how one works.  -/

@[simp]
theorem sl2_one_simp : (1:SL2) = one := rfl

@[simp]
theorem sl2_one_simp_expl : (1:SL2) = ⟨ !![(1:ℤ),0;0,1], by simp ⟩ := by
  simp[one]
  exact Matrix.one_fin_two

theorem sl2_one_simp_expl' : (1:SL2) = !![(1:ℤ),0;0,1] := by
  simp[one]
  exact Matrix.one_fin_two

/- ## Associativity

As described above, a `Semigroup` is a type that has an operation (in this case `*`) that is associative. To register this property with Lean we instantite this class as follows. -/

@[simp]
theorem sl2_mul_assoc : ∀ A B C : SL2 , A * B * C = A * ( B * C ) := by
  intro A B C
  simp[Matrix.mul_assoc]

instance inst_mod_semi: Semigroup SL2 :=
  ⟨ sl2_mul_assoc ⟩

/- ## The Identity is well behaved

Next we prove that `1` behaves like a multiplicative inverse. -/

@[simp]
theorem sl2_one_simp_left : ∀ A : SL2, 1 * A = A := by
  intro A
  simp

@[simp]
theorem sl2_one_simp_right : ∀ A : SL2, A * 1 = A := by
  intro A
  simp

instance inst_mul_one : MulOneClass SL2 :=
  ⟨ sl2_one_simp_left, sl2_one_simp_right ⟩

/- ## Inverse theorems and Group

Finally, we show that SL2 forms a group. The last ingredient is to show that inverses are well behaved.  -/

@[simp]
theorem sl2_inv_simp_left : ∀ A : SL2, A⁻¹ * A = 1 := by
  intro A
  simp[A.det1]

@[simp]
theorem sl2_inv_simp_right : ∀ A : SL2, A * A⁻¹ = 1 := by
  intro A
  simp[A.det1]

/- The group instance is then formed as follows. Note that the `Group` class lists a lot of redundant properties. The helper method `Group.ofLeftAxioms` allows use to just use the minimal set of properties and it derives the rest for us. -/

noncomputable
instance inst_mod_group : Group SL2 :=
  @Group.ofLeftAxioms SL2 _ _ _ sl2_mul_assoc sl2_one_simp_left sl2_inv_simp_left
