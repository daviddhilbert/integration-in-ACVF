import IntegrationSection6.GammaVFCoordinateIsomorphisms

/-! Point values of coordinate isomorphisms survive carrier transports. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n a r b : ℕ}

theorem gammaIsoCongrTarget_value {A : Set (Point (M := M) n a)} {C D : Set (Point (M := M) r b)}
    (e : GammaIso B A C) (he : C = D) (x : A) :
    ((e.congr rfl he).equiv x).val = (e.equiv x).val := by
  cases he
  rfl

theorem gammaVFCoordinateIso_value (A : Set (Point (M := M) n a)) (hA : GammaSetDefinable B A)
    (e : Fin r ≃ Fin n) (x : A) :
    ((gammaVFCoordinateIso A hA e).equiv x).val = (x.val.1 ∘ e,x.val.2) := by
  unfold gammaVFCoordinateIso
  rw [gammaIsoCongrTarget_value]
  rfl

end IntegrationInACVF.Section6
