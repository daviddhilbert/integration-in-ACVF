import Mathlib.Algebra.Ring.Equiv
import Section4.Imported.GrothendieckRing

/-! The canonical extension of a semiring equivalence to Grothendieck rings. -/
noncomputable section
open Algebra
namespace IntegrationInACVF.Section6
variable {A C : Type*} [CommSemiring A] [CommSemiring C]

def completionRingEquiv (e : A ≃+* C) : GrothendieckAddGroup A ≃+* GrothendieckAddGroup C := by
  let F := GrothendieckAddGroup.liftRingHom (GrothendieckAddGroup.ofRingHom.comp e.toRingHom)
  let G := GrothendieckAddGroup.liftRingHom (GrothendieckAddGroup.ofRingHom.comp e.symm.toRingHom)
  have hF (a : A) : F (GrothendieckAddGroup.of a) = GrothendieckAddGroup.of (e a) :=
    GrothendieckAddGroup.liftRingHom_apply_of _ a
  have hG (a : C) : G (GrothendieckAddGroup.of a) = GrothendieckAddGroup.of (e.symm a) :=
    GrothendieckAddGroup.liftRingHom_apply_of _ a
  refine {
    toFun := F
    invFun := G
    left_inv := ?_
    right_inv := ?_
    map_add' := map_add F
    map_mul' := map_mul F }
  · intro x
    obtain ⟨a,b,rfl⟩ := GrothendieckAddGroup.exists_eq_sub_of x
    rw [map_sub,map_sub,hF,hF,hG,hG,e.symm_apply_apply,e.symm_apply_apply]
  · intro x
    obtain ⟨a,b,rfl⟩ := GrothendieckAddGroup.exists_eq_sub_of x
    rw [map_sub,map_sub,hG,hG,hF,hF,e.apply_symm_apply,e.apply_symm_apply]

theorem completionRingEquiv_of (e : A ≃+* C) (a : A) :
    completionRingEquiv e (GrothendieckAddGroup.ofRingHom a) = GrothendieckAddGroup.ofRingHom (e a) := by
  change (GrothendieckAddGroup.liftRingHom (GrothendieckAddGroup.ofRingHom.comp e.toRingHom)) (GrothendieckAddGroup.of a) = _
  exact GrothendieckAddGroup.liftRingHom_apply_of _ a

end IntegrationInACVF.Section6
