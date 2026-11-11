import IntegrationSection3ACVF.GammaLinearValueRow
import IntegrationSection3ACVF.FullBaseLogic
import IntegrationSection3ACVF.GammaLinearRestrictions

/-! A full first-order relation for Gamma-linearity on a ball with
free radius, coefficient and centre labels. Partial function graphs
enforce actual domain containment as part of the relation. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.GammaLinearBallRow

open UniformGammaBallSyntax GammaLinearRestrictions

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def outputs (A : Set M) (f : M → M) (a : Fin 5 → M) : Prop :=
  (a 1 ∈ A ∧ a 3 = f (a 1)) ∧ (a 2 ∈ A ∧ a 4 = f (a 2)) ∧
    iVF (a 3) ∧ iVF (a 4) ∧ GammaLinearValueRow.relation (a 0) (a 1) (a 2) (a 3) (a 4)

def row (A : Set M) (f : M → M) (a : Fin 3 → M) : Prop :=
  ∀ p : Fin 2 → M, (ball (a 0) (p 0) (a 2) ∧ ball (a 0) (p 1) (a 2)) →
    ∃ q : Fin 2 → M, outputs A f ![a 1,p 0,p 1,q 0,q 1]

theorem outputs_definable (B : FullBaseAtomicity.Base (M := M)) (A : Set M) (f : M → M)
    (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f)) :
    FullBaseAtomicity.OverBase B {a : Fin 5 → M | outputs A f a} := by
  have h0 := FullBaseAtomicity.OverBase.preimage_comp hf (![1,3] : Fin 2 → Fin 5)
  have h1 := FullBaseAtomicity.OverBase.preimage_comp hf (![2,4] : Fin 2 → Fin 5)
  have hVF := ((@definableAt_iff_normalized_raw M sM hM B.real .vf _).mp
    (@definableAt_sort M sM B.real .vf)).1
  have h3 := FullBaseAtomicity.OverBase.preimage_comp (FullBaseAtomicity.OverBase.of_real (B := B) hVF)
    (fun _ : Fin 1 => (3 : Fin 5))
  have h4 := FullBaseAtomicity.OverBase.preimage_comp (FullBaseAtomicity.OverBase.of_real (B := B) hVF)
    (fun _ : Fin 1 => (4 : Fin 5))
  exact FullBaseAtomicity.OverBase.inter h0 (FullBaseAtomicity.OverBase.inter h1
    (FullBaseAtomicity.OverBase.inter h3 (FullBaseAtomicity.OverBase.inter h4 (GammaLinearValueRow.definable B))))

theorem row_definable (B : FullBaseAtomicity.Base (M := M)) (A : Set M) (f : M → M)
    (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f)) :
    FullBaseAtomicity.OverBase B {a : Fin 3 → M | row A f a} := by
  let ι := Fin 3 ⊕ Fin 2
  let υ := ι ⊕ Fin 2
  have hOutput := FullBaseAtomicity.OverBase.preimage_comp (outputs_definable B A f hf)
    (![.inl (.inl 1),.inl (.inr 0),.inl (.inr 1),.inr 0,.inr 1] : Fin 5 → υ)
  have hExist := FullBaseAtomicity.OverBase.exists_block hOutput
  have hBall0 := FullBaseAtomicity.OverBase.preimage_comp (ball_definable B)
    (![.inl 0,.inr 0,.inl 2] : Fin 3 → ι)
  have hBall1 := FullBaseAtomicity.OverBase.preimage_comp (ball_definable B)
    (![.inl 0,.inr 1,.inl 2] : Fin 3 → ι)
  have hPrem := FullBaseAtomicity.OverBase.inter hBall0 hBall1
  have hd := FullBaseAtomicity.OverBase.forall_block (FullBaseLogic.implication B hPrem hExist)
  apply FullBaseAtomicity.OverBase.congr hd
  intro a
  rfl

theorem row_iff (A : Set M) (f : M → M) (hfVF : ∀ x ∈ A, iVF (f x))
    (r s : M) (hr : NonzeroRV r) (hs : NonzeroRV s) (c : VFType (M := M)) :
    row A f ![r,s,c.val] ↔ SlopeAt A f hfVF c (codeValue r) (codeValue s) := by
  constructor
  · intro hRow
    have hSub : GammaRadiusAtomicity.gammaBall c (codeValue r) true ⊆ A := by
      intro y hy
      let Y : VFType (M := M) := ⟨y,hy.1⟩
      have hY := (ball_iff r hr Y c).mpr hy
      obtain ⟨q,hq⟩ := hRow ![y,y] ⟨hY,hY⟩
      exact hq.1.1
    refine ⟨hSub,?_⟩
    intro x y hx hy
    have hxB := (ball_iff r hr x c).mpr hx
    have hyB := (ball_iff r hr y c).mpr hy
    obtain ⟨q,hq⟩ := hRow ![x.val,y.val] ⟨hxB,hyB⟩
    obtain ⟨⟨hxA,hqx⟩,⟨hyA,hqy⟩,hu,hv,hValue⟩ := hq
    let U : VFType (M := M) := ⟨q 0,hu⟩
    let V : VFType (M := M) := ⟨q 1,hv⟩
    have hEq := (GammaLinearValueRow.relation_iff s hs x y U V).mp hValue
    have hU : U = ⟨f x.val,hfVF _ hxA⟩ := Subtype.ext hqx
    have hV : V = ⟨f y.val,hfVF _ hyA⟩ := Subtype.ext hqy
    rw [hU,hV] at hEq
    exact hEq
  · rintro ⟨hSub,hLinear⟩ p ⟨hxB,hyB⟩
    let x : VFType (M := M) := ⟨p 0,hxB.1⟩
    let y : VFType (M := M) := ⟨p 1,hyB.1⟩
    have hx := (ball_iff r hr x c).mp hxB
    have hy := (ball_iff r hr y c).mp hyB
    let u : VFType (M := M) := ⟨f (p 0),hfVF _ (hSub hx)⟩
    let v : VFType (M := M) := ⟨f (p 1),hfVF _ (hSub hy)⟩
    refine ⟨![u.val,v.val],⟨hSub hx,rfl⟩,⟨hSub hy,rfl⟩,u.property,v.property,?_⟩
    exact (GammaLinearValueRow.relation_iff s hs x y u v).mpr (hLinear x y hx hy)

end IntegrationInACVF.Section3ACVF.GammaLinearBallRow
