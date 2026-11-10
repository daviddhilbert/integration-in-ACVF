import IntegrationSection3ACVF.RVSlopeControllers
import IntegrationSection3ACVF.FiniteControllerTails
import IntegrationSection3ACVF.GammaTailMap

/-! The actual RV coefficient is eventually constant on the source Gamma
tail. This does not assert constancy down to the source-ball radius. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity

namespace IntegrationInACVF.Section3ACVF.RVSlopeTail

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem eventual_relation {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : FullBaseAtomicity.Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    (a : VFType (M := M)) (α : Values.Gamma (M := M))
    (hA : AdjoinBall.AtomicOver B (gammaBall a α true))
    (f : M → M) (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn (gammaBall a α true) f))
    (hfVF : ∀ x ∈ gammaBall a α true, iVF (f x)) (hinj : Set.InjOn f (gammaBall a α true)) :
    ∃ η : Values.Gamma (M := M), α < η ∧ ∃ c : M, NonzeroRV c ∧
      ∀ γ : Values.Gamma (M := M), η < γ → RVSlopeGamma.relation (gammaBall a α true) f γ c := by
  have ho : PaperBalls.IsOpenBall (gammaBall a α true) := Or.inr ⟨a,α,rfl⟩
  have hFin := RVSlopeGamma.finite_image hκ hs B hsmall h00 δ hδ hδ1 ho hA f hf hfVF hinj
  have hDomain (γ : Values.Gamma (M := M)) (hαγ : α < γ) :
      ∃ c : M, RVSlopeGamma.relation (gammaBall a α true) f γ c :=
    (GammaSlopeDomain.domain_iff a α γ f hfVF hinj).mpr hαγ
  obtain ⟨η,hαη,c,hR⟩ := FiniteControllerTails.eventual_label
    (RVSlopeGamma.relation (gammaBall a α true) f) α hFin hDomain
    (fun c => RVSlopeControllers.row_controller h00 B hf c)
  obtain ⟨γ,hηγ⟩ := exists_gt η
  obtain ⟨t,_,ht⟩ := hR γ hηγ
  exact ⟨η,hαη,c,ht.2.1,hR⟩

theorem eventual_coefficient {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : FullBaseAtomicity.Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    (a : VFType (M := M)) (α : Values.Gamma (M := M))
    (hA : AdjoinBall.AtomicOver B (gammaBall a α true))
    (f : M → M) (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn (gammaBall a α true) f))
    (hfVF : ∀ x ∈ gammaBall a α true, iVF (f x)) (hinj : Set.InjOn f (gammaBall a α true)) :
    ∃ η : Values.Gamma (M := M), α < η ∧ ∃ c : M, NonzeroRV c ∧
      ∀ γ : Set.Ioi α, η < γ.val → GammaTailMap.coefficient a α f hfVF hinj γ = c := by
  obtain ⟨η,hαη,c,hc,hR⟩ := eventual_relation hκ hs B hsmall h00 δ hδ hδ1 a α hA f hf hfVF hinj
  refine ⟨η,hαη,c,hc,fun γ hηγ => ?_⟩
  have ho : PaperBalls.IsOpenBall (gammaBall a α true) := Or.inr ⟨a,α,rfl⟩
  exact RVSlopeConstancy.on_value_fibre B h00 δ hδ hδ1 ho hA f hf hfVF hinj γ.val
    (GammaTailMap.coefficient_spec a α f hfVF hinj γ) (hR γ.val hηγ)

end IntegrationInACVF.Section3ACVF.RVSlopeTail
