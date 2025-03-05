/- # Modular Group

In this file we define the modular group using the following Mathlib data structures:

  * Matrix.SpecialLinearGroup (Fin 2) ℤ. We abbreviate this type by SL2. It is the 2x2 integer matricies with determinant 1
  * Subgroup. We define the set containing I and -I and show it its a subgroup of SL2.
  * SL2⧸IMI. The quotient type where A ≃ -A for all A in SL2.
  * Subgroup.normal : Instantiates SL2⧸IMI as a group by showing that IMI is a *normal* subgroup (meaning it's elements are invariant under conjugation) -/

import Mathlib.tactic
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Data.Finset.Basic
import Mathlib.GroupTheory.Coset.Defs

/- We abbreviate SL2 and define the distinguished elements that will serve as generators later. -/

abbrev SL2 := Matrix.SpecialLinearGroup (Fin 2) ℤ
def T : SL2  := ⟨ !![1,1;0,1], by simp ⟩
def S : SL2  := ⟨ !![0, -1; 1, 0], by simp ⟩

/- We define IMI to be the subgroup of SL2 consisting of I and -I. -/

instance IMI : Subgroup SL2 where

  carrier := { 1, -1 }

  mul_mem' := by
    intro A B ha hb
    apply Or.elim ha
    . apply Or.elim hb
      . intro h1 h2; simp[h1, h2]
      . intro h1 h2; simp[h1, h2]
    . apply Or.elim hb
      . intro h1 h2; simp[h1, h2]
      . intro h1 h2; simp[h1, h2]
        apply Or.inl
        have h1 : B = -1 := by exact h1
        have h2 : A = -1 := by exact h2
        simp[h1,h2]

  one_mem' := by exact Set.mem_insert 1 {-1}

  inv_mem' := by simp_all

/- The quotiented elements corresponding to S and T can now be defined. -/

def Tq : SL2 ⧸ IMI := QuotientGroup.mk T
def Sq : SL2 ⧸ IMI := QuotientGroup.mk S

/- The quotient is just a type until we instantiate it as a group. In particular, Lean doesn't know SL2 ⧸ IMI is a group unless we show that IMI is a normal subgroup of SL2, and so group operations don't work. -/

def get_one (G : Type*) [Group G] := (1:G) -- example function that requires a group

#check SL2 ⧸ IMI
#check_failure Tq*Tq
#check_failure get_one (SL2⧸IMI)

/- If you show that IMI is a normal subgroup, then magically SL2⧸IMI gets instantiated as a Group. -/

theorem imi_elements (A : SL2) : A ∈ IMI → A = 1 ∨ A = (-1:SL2)  := by
  intro ha
  exact ha

instance normal : Subgroup.Normal IMI :=
  ⟨
    by -- Show ∀ A ∈ IMI, ∀ (B : SL2), A * B * A⁻¹ ∈ IMI
      intro A hm B
      by_cases h1 : A = 1
      . rw[h1]
        simp[IMI]
      . have : A = -1 := by
          apply imi_elements at hm
          apply Or.elim hm
          . exact fun a ↦ False.elim (h1 a)
          . exact fun a ↦ a
        rw[this]
        simp[IMI]
  ⟩

#check Tq*Tq
#check get_one (SL2⧸IMI)
