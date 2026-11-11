import IntegrationSection4.LinearBallRadius
import IntegrationSection4.InverseBodies

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section5
open IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section4.CompatibleFibreSlopes

open GammaRadiusAtomicity

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- The nondegenerate compatible-fibre formula in Remark 4.6. Both RV
classes are ordinary; the displayed ratio therefore lies in Gamma. -/
theorem ratio {S₁ S₂ : Set M} {m₁ m₂ l₁ l₂ : ℕ}
    {A : DefSet (M := M) S₁ 1 m₁} {B : DefSet (M := M) S₁ 1 l₁}
    {C : DefSet (M := M) S₂ 1 m₂} {D : DefSet (M := M) S₂ 1 l₂}
    (T₁ : SpecialBijection A B) (T₂ : SpecialBijection C D)
    (hB : IsRVPullback (carrier B)) (hD : IsRVPullback (carrier D))
    (b : B) (d : D) (hb : vfAt b.val 0 ≠ 0) (hd : vfAt d.val 0 ≠ 0)
    (U : Set M) (f : M → M) (hfVF : ∀ x ∈ U, iVF (f x))
    (s : Values.Gamma (M := M)) (hLin : GammaLinearity.GammaLinear U f hfVF s)
    (hSub : InverseBodies.body T₁ b ⊆ U)
    (hImage : f '' InverseBodies.body T₁ b = InverseBodies.body T₂ d) :
    s.val = Values.vfValueHom (vfAt d.val 0) / Values.vfValueHom (vfAt b.val 0) := by
  obtain ⟨α,hα,hSource⟩ := InverseBodies.body_ordinary T₁ hB b hb
  obtain ⟨β,hβ,hTarget⟩ := InverseBodies.body_ordinary T₂ hD d hd
  have hSub' : gammaBall (vfAt (T₁.inverseMap b).val 0) α true ⊆ U := hSource ▸ hSub
  have hI : f '' gammaBall (vfAt (T₁.inverseMap b).val 0) α true =
      gammaBall (vfAt (T₂.inverseMap d).val 0) β true := by
    rwa [hSource,hTarget] at hImage
  have hs := LinearBallRadius.slope_eq (vfAt (T₁.inverseMap b).val 0)
    (vfAt (T₂.inverseMap d).val 0) α β s f (fun x hx => hfVF x (hSub' hx))
    (fun x y hx hy => hLin x y (hSub' hx) (hSub' hy)) hI
  rw [hs,div_eq_mul_inv,Values.gamma_val_mul,Values.gamma_val_inv,← hα,← hβ,div_eq_mul_inv]

end IntegrationInACVF.Section4.CompatibleFibreSlopes
