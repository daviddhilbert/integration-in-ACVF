import IntegrationSection4.TranslatedRVGeometry

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section5
open IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section4.LinearRVClasses

open BalancedFibres Cells GammaRadiusAtomicity

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- A Gamma-linear open-to-open map sends each entire nonzero difference
RV class to its entire output difference class. This is equality of actual
point sets, including the reverse containment needed for balanced fibres. -/
theorem image_class (A : Set M) (ho : PaperBalls.IsOpenBall A) (f : M → M)
    (hfVF : ∀ x ∈ A, iVF (f x)) (hInj : Set.InjOn f A)
    (hoo : MaximalOpenClasses.OpenToOpen A f) (s : Values.Gamma (M := M))
    (hLin : GammaLinearity.GammaLinear A f hfVF s)
    (a x fa fx : VF (M := M)) (ha : a.val ∈ A) (hx : x.val ∈ A) (hne : x ≠ a)
    (hfa : f a.val = fa.val) (hfx : f x.val = fx.val) :
    f '' rawSet (translatedRV (rv (x-a)) a) =
      rawSet (translatedRV (rv (fx-fa)) fa) := by
  let u := rv (x-a)
  have hu : u ≠ rv (0 : VF (M := M)) := by
    intro h
    have hz := (rv_eq_zero_iff (x-a)).mp h
    exact hne (sub_eq_zero.mp hz)
  let γ : Values.Gamma (M := M) := ⟨Values.vrv u,TranslatedRVGeometry.value_ne_infinity u hu⟩
  let C := rawSet (translatedRV u a)
  have hxC : x ∈ translatedRV u a := rfl
  have hC : C = gammaBall x γ true := TranslatedRVGeometry.ordinary_ball u hu a x hxC
  have hCA : C ⊆ A := TranslatedRVGeometry.subset_open ho u a x ha hx hxC
  have hBallA : gammaBall x γ true ⊆ A := hC ▸ hCA
  let v := rv (fx-fa)
  have hv : v ≠ rv (0 : VF (M := M)) := by
    intro h
    have hz := sub_eq_zero.mp ((rv_eq_zero_iff (fx-fa)).mp h)
    exact hne (Subtype.ext (hInj hx ha (hfx.trans ((congrArg Subtype.val hz).trans hfa.symm))))
  let β : Values.Gamma (M := M) := ⟨Values.vrv v,TranslatedRVGeometry.value_ne_infinity v hv⟩
  have hValue := hLin a x ha hx
  have hfa' : (⟨f a.val,hfVF _ ha⟩ : VFType (M := M)) = fa := Subtype.ext hfa
  have hfx' : (⟨f x.val,hfVF _ hx⟩ : VFType (M := M)) = fx := Subtype.ext hfx
  change Values.vfValueHom ((_ : VFType (M := M))-(_ : VFType (M := M))) =
    s.val * Values.vfValueHom (x-a) at hValue
  rw [hfa',hfx'] at hValue
  have hRadius : s*γ = β := by
    apply Subtype.ext
    exact hValue.symm
  have hImage : f '' C = gammaBall fx (s*γ) true := by
    rw [hC]
    have hL : GammaLinearity.GammaLinear (gammaBall x γ true) f
        (fun y hy => hfVF y (hBallA hy)) s :=
      fun y z hy hz => hLin y z (hBallA hy) (hBallA hz)
    have H := LinearBallRadius.image_ball x γ s f _ hL ((hoo _ hBallA).mp (Or.inr ⟨x,γ,rfl⟩))
    have he : (⟨f x.val,hfVF _ (hBallA (BallEnlargementGeometry.gammaBall_centre_mem x γ true))⟩ : VFType (M := M)) = fx := Subtype.ext hfx
    rw [he] at H
    exact H
  have hOut := TranslatedRVGeometry.ordinary_ball v hv fa fx (show fx ∈ translatedRV v fa from rfl)
  exact hImage.trans (by rw [hRadius]; exact hOut.symm)

end IntegrationInACVF.Section4.LinearRVClasses
