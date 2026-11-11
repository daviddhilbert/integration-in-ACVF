import IntegrationSection3ACVF.GammaLinearRadiusSyntax
import IntegrationSection3ACVF.LeastLinearRadiusGeometry

/-! Least actual linear-radius existence for ordinary open source balls.
The VF boundary is handled separately: its identity has no least
GammaTop radius. No existence conclusion is obtained by definition. -/

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.LeastLinearRadiusExistence

open GammaRadiusAtomicity LinearRadiusThreshold

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem ordinary (h00 : M ⊨ Axioms.ACVF00) (B : FullBaseAtomicity.Base (M := M))
    (a : VFType (M := M)) (α : Values.Gamma (M := M)) (f : M → M)
    (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn (gammaBall a α true) f))
    (hfVF : ∀ x ∈ gammaBall a α true, iVF (f x)) (c : VFType (M := M)) (hc : c.val ∈ gammaBall a α true) :
    ∃ r : Values.GammaTop (M := M), IsLeastLinearRadius (gammaBall a α true) f hfVF c r :=
  LeastLinearRadiusGeometry.exists_least_of_definable h00 (RealParameterTuples.extend B ![c.val])
    _ f hfVF c hc (GammaLinearRadiusSyntax.locus_definable B _ f hf hfVF c)
    (LeastLinearRadiusGeometry.ordinary_locus_bounded a c α f hfVF)

theorem ordinary_function (h00 : M ⊨ Axioms.ACVF00) (B : FullBaseAtomicity.Base (M := M))
    (a : VFType (M := M)) (α : Values.Gamma (M := M)) (f : M → M)
    (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn (gammaBall a α true) f))
    (hfVF : ∀ x ∈ gammaBall a α true, iVF (f x)) :
    ∃ threshold : VFType (M := M) → Values.GammaTop (M := M), ∀ c : VFType (M := M),
      c.val ∈ gammaBall a α true → IsLeastLinearRadius (gammaBall a α true) f hfVF c (threshold c) := by
  classical
  have hChoice (c : VFType (M := M)) : ∃ r : Values.GammaTop (M := M),
      c.val ∈ gammaBall a α true → IsLeastLinearRadius (gammaBall a α true) f hfVF c r := by
    by_cases hc : c.val ∈ gammaBall a α true
    · obtain ⟨r,hr⟩ := ordinary h00 B a α f hf hfVF c hc
      exact ⟨r,fun _ => hr⟩
    · exact ⟨Values.infinity,fun h => (hc h).elim⟩
  choose threshold hThreshold using hChoice
  exact ⟨threshold,hThreshold⟩

theorem corollary_3_17_ordinary {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : FullBaseAtomicity.Base (M := M)) (hsmall : Cardinal.mk B.real < κ) (h00 : M ⊨ Axioms.ACVF00)
    (a : VFType (M := M)) (α : Values.Gamma (M := M)) (f : M → M)
    (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn (gammaBall a α true) f))
    (hfVF : ∀ x ∈ gammaBall a α true, iVF (f x)) (hInj : Set.InjOn f (gammaBall a α true)) :
    ∃ threshold : VFType (M := M) → Values.GammaTop (M := M),
      (∀ c : VFType (M := M), c.val ∈ gammaBall a α true →
        IsLeastLinearRadius (gammaBall a α true) f hfVF c (threshold c)) ∧
      ¬ ∃ β : Values.Gamma (M := M), α < β ∧
        ∀ c : VFType (M := M), c.val ∈ gammaBall a α true → β.val < threshold c := by
  obtain ⟨threshold,hThreshold⟩ := ordinary_function h00 B a α f hf hfVF
  refine ⟨threshold,hThreshold,?_⟩
  have hNo := LinearRadiusThreshold.corollary_3_17 hκ hs B hsmall h00
    (Or.inr ⟨a,α,rfl⟩) f hf hfVF hInj (↑α.val : PaperBalls.Radius (M := M))
    (Or.inr (Or.inr ⟨a,α,true,rfl,rfl⟩)) threshold hThreshold
  rintro ⟨β,hαβ,hAll⟩
  exact hNo ⟨β,WithBot.coe_lt_coe.mpr hαβ,hAll⟩

end IntegrationInACVF.Section3ACVF.LeastLinearRadiusExistence
