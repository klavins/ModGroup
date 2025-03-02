

<center><h1>The Modular Group</h1></center>
<center><h2>EE 546 : Automated Reasoning<br />
            Example Project Structure</h2></center>

<center>
Department of Electrical and Computer Engineering<br />
Unviersity of Washington<br />
Prof. Eric Klavins<br />
Winter 2025
</center>
<br />

 # Introduction

The *modular group* is the set of 2x2 matrcies with integer entries and determinant 1 under the operation of matrix multiplication. That is,

  $$
  SL_2(\mathbb{Z}) =
  \left \lbrace
  \begin{pmatrix}
  a & b\\
  c & d
  \end{pmatrix}\;|\;a,b,c,d\in \mathbb{Z};, \;ad - bc = 1
  \right \rbrace.
  $$

Here, SL₂(ℤ) stands for *Special Linear Group* of dimension 2 over the integers. An alternative characterization of the Modular group is as the set of integer fractional linear transformations, FLT(ℤ), of the form

   $$
    z \mapsto \frac{az+b}{cz+d}
   $$

where $a$, $b$, $c$ and $d$ are integers, $a*c - b*d = 1$ and $z \in \mathbb{C}$ with $\mathrm{im}(z) > 0$. In this case, the group operation is function composition. This latter characterization provides an incredibly rich relationship between the integers and the complex numbers.

In this project, we show the following in Lean 4:

- SL₂(ℤ) is a group.
- FLT(ℤ) is group.
- SL₂(ℤ) and FLT(ℤ) are isomorphic.

To acheive this goal, we define three new types:

- `SL2` to represent the 2x2 special linear group over the integers and defined in Lib/SL2.lean
- `UHP` to represent the upper half of the complex plane and defined in Lib/UHP.lean
- `FLT` to represent integer valued fractional linear transformations, defined in Lib/FLT.lean

I also built a library of helpers for basic manipmulations and coercions of complex numbers, which can be found in Lib/Complex.Lib. All of the above types rely on Mathlib and in particular the encoding of Complex Numbers, Matrices, Linear Algebra, and Groups. And of course, Mathlib's Tactics library is used extensively for the proofs. 
```hs
import ModGroup.Lib.Complex
import ModGroup.Lib.UHP
import ModGroup.Lib.SL2
import ModGroup.Lib.FLT
open Complex
```
 ## Resources

Each of the above libraries contains documentation specific to the enclosed types and the associated theorems. This README file gives an overview of the results and several examples.

The mathematics of modular groups can be found in a variety of places. I have mainly used the following resources:

- Fred Diamond and Jerry Shurman, *A First Course In Modular Forms*, *Springer*, 2005.
- Hugh Montgomery's notes on fractional linear transformations, which can be found [here](https://public.websites.umich.edu/~hlm/nzm/modgp.pdf).
 # SL2

The `SL2` type is definied as a structure containing a 2x2 integer matrix and a proof that it has determinant one. In Lean this is expressed as follows (we use a temporary namespace to avoid naming conflicts):  
```hs
namespace Temp

@[ext]
structure SL2 where
  val : Matrix (Fin 2) (Fin 2) ℤ
  det1 : val.det = 1 := by decide

end Temp
```

 Following standard Lean, elements cam be defined in  n a variety of ways. First, we can use the default constructe `mk`. In the second case below, we use the default proof for the determinant property.

```hs
#check SL2.mk !![1,1;0,1] rfl
#check SL2.mk !![1,1;0,1]
```
 Or we can use curly braces and the `:` operator to inform Lean what type we are building. 
```hs
#check ({val:=!![1,1;0,1], det1 := rfl} : SL2)
#check ({val:=!![1,1;0,1]} : SL2)
```
  We can also use angle brackets: 
```hs
#check (⟨!![1,1;0,1], rfl⟩ : SL2)
```
 And of course if we do not supply an integer matrix or a determinant 1 matrix, the construction fails. 
```hs
#check_failure SL2.mk !![(a:ℝ),1;1,0]
#check_failure SL2.mk !![1,1;1,1]
```
 ## Distinguished Elements

Two distinguished elements in SL2 are the following matrices:

  $$
  T = \begin{pmatrix}
  1 & 1\\
  1 & 0
  \end{pmatrix} {  } \mathrm{and} {  }
  W = \begin{pmatrix}
  0 & -1\\
  1 & 0
  \end{pmatrix}
  $$

These elements are said to *generate* SL2, because every element of SL2 can be formed from a combination of $T$, $S$ and their inverses, although -- sadly -- we do not (yet) prove this fact in this project.  
```hs
def T := SL2.mk !![1,1;0,1]
def S := SL2.mk !![0, -1; 1, 0]
```
 ## Coercion

Elements in SL2 can be coerced to matrices so that one does not need to write, for example, $S.val$.   
```hs
#check S*T
#check S 0 0
```

```hs
## Operations on Elements of SL2

Elements in SL2 hav all the same properties as invertible 2x2 matrices, including multiplication, inverses, and a distinguished identity element.  -/

#check S*T
#eval S*T
#check T⁻¹
#check T * 1
```
 ### Example Calculation

All of the instances required to prove `SL2` is a Group are defined in Lib/SL2.lean. Thus, we can use Mathlib's built in simplification rules for groups either directly, or by just calling the `group` tactic. 
```hs
example (A B : SL2): (A⁻¹*B*A)⁻¹ = A⁻¹*B⁻¹*A :=
  calc (A⁻¹*B*A)⁻¹
  _  = A⁻¹ * (A⁻¹*B)⁻¹   := by rw[DivisionMonoid.mul_inv_rev]
  _  = A⁻¹ * (B⁻¹*A⁻¹⁻¹) := by rw[DivisionMonoid.mul_inv_rev]
  _  = A⁻¹ * (B⁻¹*A)     := by rw[DivisionMonoid.inv_inv]
  _  = A⁻¹ * B⁻¹ * A     := by rw[Semigroup.mul_assoc]

example (A B : SL2): (A⁻¹*B*A)⁻¹ = A⁻¹*B⁻¹*A := by group
```
 ## Examples

Here are some examples that use the definitions and theorems for SL2.  
```hs
example : ¬ ∀ A B : SL2, A*B = B*A := by
  intro h
  have h1 := h S T
  have h2 : (S*T).val 0 0 = (T*S).val 0 0 := by simp[h1]
  simp[S,T] at h2

example : ∀ A B : SL2, (A*B)⁻¹ = B⁻¹ * A⁻¹ := by
  intro A B
  group

example : ∀ A : SL2, A⁻¹*A = 1 := by
  intro A
  group

example : S*T ≠ T*S := by
  intro h
  have h2 : (S*T).val 0 0 = (T*S).val 0 0 := by simp[h]
  simp[S,T] at h2

example (A B C : SL2) : A * (B * C) * (A * C)⁻¹ * (A * B * A⁻¹)⁻¹ = 1 := by
  group
```
 # Fractional Linear Transformations

As described above, an fractional linear transformation has the form

   $$
    z \mapsto \frac{az+b}{cz+d}.
   $$

In general, $a$, $b$, $c$ and $d$ can come from any ring, and the only requirement is that $ad+bc \ne 0$. Here, we additionally require that $a$, $b$, $c$ and $d$ are integers and $ad+bc = 1$. To keep track over everything, we pack everything into a structure and, with an abuse of naming, call it an`FLT`:  
```hs
namespace Temp

@[ext]
structure FLT where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  det1 : a*d - b*c = 1 := by decide

end Temp
```
 The main accomplishment of this section is to define the map assocated with an FLT, which we call fl_map. 
```hs
#check fl_map      -- fl_map (f : FLT) (z : UHP) : UHP
```
 Specifically, we needed to show that the map so defined produces an element of `UHP` when given an element of `UHP`. We used the proof of this fact from [these](https://public.websites.umich.edu/~hlm/nzm/modgp.pdf) lecture notes, which explains the result as follows. Letting $z = x + yi$, with y > 0, we get

$$
w \triangleq \frac{az+b}{cz+d} = \frac{az+b}{cz+d} \frac{c\bar{z}+d}{c\bar{z}+d}
$$

$$
= \frac{ac(x^2+y^2)+(bc+ad)x+bd}{(cx+d)^2+(cy)^2} +
 i\frac{(ad-bc)y}{(cx+d)^2+(cy)^2}.
$$

Since $ad+bc = 1$, we conclude that $(cx+d)^2+(cy)^2>0$ and $(ad+bc)y>0$. The proof of this shows up in Lib/FLT.lean, is 60 lines long, and uses about 14 helper lemmas defined several hundred lines of code. Clearly, there is room for improvement.

 ## USING FLTs

In Lib/FLT.lean, we instantiate all the classes needed to show that the FLT structure is a group, as well as coerce it appropriately. Thus, all the following examples work. 
```hs
example (f: FLT) (z : UHP) : f z = f z := rfl

example (f: FLT) : f * f⁻¹ = 1 := by group

example (f g h : FLT) : f * (g * h) * (f * h)⁻¹ * (f * g * f⁻¹)⁻¹ = 1 := by group
```
 # SHOWING SL2 ≅ FLT

Given the similarity between the definitions of SL2 and FLT in terms of $a$, $b$, $c$, and $d$ and the determinant condition, it should come as no surprise that the two groups we instantiated above are essentially the same.

Mathematically, we say they isomorphic, which means: There exists a function φ from the elemtns of `SL2` to the elements of `FLT` that is *bijective* and for all $A$ and $B$ in `SL2`,

  $$
    \phi(A) \circ \phi(B) = \phi(AB)
  $$

In Lib/FLT.lean, we define to maps: `fl_to_sl2` and `sl2_to_fl` that serve as witnesses to this fact. And we prove two theorems, which simply show that we are doing our book-keeping with $a$, $b$, $c$, and $d$ correctly: 
```hs
#check sl2_map_map   -- sl2_to_fl ∘ fl_to_sl2 = id
#check fl_map_map    -- fl_to_sl2 ∘ sl2_to_fl = id
```
 ## Bijective

Either one of these facts is enough to show a function is a bijection. Lean provides the necessary definitions and theorems in the Prelude.  
```hs
theorem li : Function.LeftInverse fl_to_sl2 sl2_to_fl  := by
  intro x
  simp[fl_to_sl2,sl2_to_fl,SL2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem ri : Function.RightInverse fl_to_sl2 sl2_to_fl := by exact congrFun rfl

theorem bijective_sl2_to_fl : Function.Bijective sl2_to_fl := by
  apply And.intro
  . apply Function.LeftInverse.injective li
  . apply Function.RightInverse.surjective ri
```
 ## FLT and SL2 are Isomorphic

To show the precise form of the fact that group operation is preserved by the bijection, we use a theorem proved in Lib/FLT.lean.  
```hs
theorem flt_sl2_group_iso (f g : FLT) : fl_to_sl2 f * fl_to_sl2 g = fl_to_sl2 (f*g) := by
  apply Eq.symm
  rw[←fl_comp_sl2_iff]
```
