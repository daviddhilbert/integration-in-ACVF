import IntegrationSection3ACVF.GammaLinearRadiusClosure
import IntegrationSection3ACVF.ParameterizedOpenImages
import IntegrationSection3ACVF.LinearRadiusThreshold
import IntegrationSection3ACVF.RealParameterTuples

/-! A uniform linear-radius relation on an ordinary ball forces linearity
on that whole ball. Local linear balls come from the checked 3.17 geometry;
closedness at the boundary avoids choosing a least-radius function. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section4.ConstantRowsLinearity

open GammaRadiusAtomicity GammaLinearRestrictions

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem on_ordinary_ball {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : FullBaseAtomicity.Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (h00 : M ⊨ Axioms.ACVF00) (A : Set M) (f : M → M)
    (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f))
    (hfVF : ∀ x ∈ A, iVF (f x)) (hInj : Set.InjOn f A)
    (c : VFType (M := M)) (ρ : Values.Gamma (M := M))
    (hEA : gammaBall c ρ true ⊆ A)
    (hRows : ∀ x y : VFType (M := M), x.val ∈ gammaBall c ρ true →
      y.val ∈ gammaBall c ρ true → ∀ β s : Values.Gamma (M := M),
        SlopeAt A f hfVF x β s ↔ SlopeAt A f hfVF y β s) :
    ∃ s : Values.Gamma (M := M),
      GammaLinearity.GammaLinear (gammaBall c ρ true) f (fun x hx => hfVF x (hEA hx)) s := by
  let E := gammaBall c ρ true
  have hEOpen : PaperBalls.IsOpenBall E := Or.inr ⟨c,ρ,rfl⟩
  obtain ⟨q,_,hqE⟩ := ParameterizedOpenImages.exists_open_code hEOpen
  let C := RealParameterTuples.extend B q
  have hE : FullBaseAtomicity.OverBase C {z : Fin 1 → M | z 0 ∈ E} := by
    have hd := RealParameterTuples.specialize B q (OpenImageConfigurations.body_definable B)
    apply FullBaseAtomicity.OverBase.congr hd
    intro z
    change z 0 ∈ OpenImageConfigurations.body q ↔ z 0 ∈ E
    rw [hqE]
  have hGraph : FullBaseAtomicity.OverBase C (ImaginaryBaseImages.graphOn E f) := by
    apply FullBaseAtomicity.OverBase.congr
      (FullBaseAtomicity.OverBase.inter
        (FullBaseAtomicity.OverBase.preimage_comp hE (fun _ : Fin 1 => (0 : Fin 2)))
        (RealParameterTuples.mono B q hf))
    intro z
    change (z 0 ∈ E ∧ z 0 ∈ A ∧ z 1 = f (z 0)) ↔ (z 0 ∈ E ∧ z 1 = f (z 0))
    exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,hEA h.1,h.2⟩⟩
  have hEVF : ∀ x ∈ E, iVF (f x) := fun x hx => hfVF x (hEA hx)
  have hEInj : Set.InjOn f E := fun _ hx _ hy he => hInj (hEA hx) (hEA hy) he
  have hCC : c.val ∈ E := BallEnlargementGeometry.gammaBall_centre_mem c ρ true
  have hAll (β : Values.Gamma (M := M)) (hρβ : ρ < β) :
      β ∈ GammaLinearRadiusClosure.locus A f hfVF c := by
    obtain ⟨x,hx,hSub,s,hLin⟩ := LinearRadiusThreshold.exists_at_radius hκ hs C
      (RealParameterTuples.small hκ B hsmall q) h00 hEOpen f hGraph hEVF hEInj
      (↑ρ.val : PaperBalls.Radius (M := M)) (Or.inr (Or.inr ⟨c,ρ,true,rfl,rfl⟩)) β
      (WithBot.coe_lt_coe.mpr hρβ)
    have hSub' : gammaBall x β true ⊆ E := (LinearRadiusThreshold.ballAt_gamma x β) ▸ hSub
    have hSlope : SlopeAt A f hfVF x β s := by
      refine ⟨hSub'.trans hEA,?_⟩
      intro y z hy hz
      exact hLin y z ((LinearRadiusThreshold.ballAt_gamma x β).symm ▸ hy)
        ((LinearRadiusThreshold.ballAt_gamma x β).symm ▸ hz)
    exact ⟨s,(hRows x c hx hCC β s).mp hSlope⟩
  obtain ⟨s,hSub,hLin⟩ := GammaLinearRadiusClosure.closed_above A f hfVF c ρ hAll
  exact ⟨s,hLin⟩

end IntegrationInACVF.Section4.ConstantRowsLinearity
