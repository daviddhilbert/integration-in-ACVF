import IntegrationSection3ACVF.FullGammaRadius
import Section4.GammaNamedValue

/-! Defining an actual ball after finitely naming a centre and a radius code. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section4
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity
open IntegrationInACVF.Section3ACVF.BallCosetAtomicity

namespace IntegrationInACVF.Section3ACVF.NamedBallSetup

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem gamma_scalar_of_code (h00 : M ⊨ Axioms.ACVF00)
    (B : FullBaseAtomicity.Base (M := M)) (γ : Values.Gamma (M := M))
    (t : CanonicalRV.RVSort M) (ht0 : t.val ≠ iRVZero)
    (htγ : Values.vrv t = γ.val) (htB : t.val ∈ B.real) :
    FullGammaSyntax.Scalar B {γ} := by
  have hd := gammaDcl_of_named_code h00 t.val htB ⟨t.property,ht0⟩
  have he : Values.gammaOf t ht0 = γ := Subtype.ext htγ
  rw [he] at hd
  exact FullGammaSyntax.Scalar.of_real hd

theorem cosetBody_definable (B : FullBaseAtomicity.Base (M := M))
    (H : AddSubgroup (VFType (M := M)))
    (hH : FullBaseAtomicity.OverBase B
      {z : Fin 1 → M | z 0 ∈ Subtype.val '' (H : Set (VFType (M := M)))})
    (a : VFType (M := M)) (ha : a.val ∈ B.real) :
    FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ cosetBody H a} := by
  have hr := FullBallCoset.cosetRelation_definable B H hH
  have hm : @Set.DefinableMap M LRV (CanonicalStructure.normalize (M := M))
      (Fin 1) (Fin 2) B.real (fun z => ![a.val,z 0]) := by
    letI := CanonicalStructure.normalize (M := M)
    intro j
    fin_cases j
    · exact LRV.definableFun_const (Fin 1) ha
    · exact Set.DefinableFun.proj LRV
  have hd := FullBaseAtomicity.OverBase.preimage_map hr hm
  apply FullBaseAtomicity.OverBase.congr hd
  intro z
  exact Set.ext_iff.mp (cosetRelation_fibre H a) (z 0)

theorem gammaBall_definable (B : FullBaseAtomicity.Base (M := M))
    (a : VFType (M := M)) (ha : a.val ∈ B.real)
    (γ : Values.Gamma (M := M)) (hγ : FullGammaSyntax.Scalar B {γ}) :
    FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ gammaBall a γ true} := by
  obtain ⟨H,hH,hcosets⟩ := FullGammaRadius.gamma_subgroup B γ hγ true
  have hd := cosetBody_definable B H hH a ha
  rwa [hcosets a] at hd

end IntegrationInACVF.Section3ACVF.NamedBallSetup
