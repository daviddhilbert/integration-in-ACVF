import IntegrationSection6.GammaVFParameterBases
import IntegrationSection6.MixedCoordinatePointMaps
import IntegrationSection6.GammaRVFamilyFormulas

/-! The actual mixed source of a VF-parameter RV family retains its
complete original-Gamma definition over a definable VF base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a k : ℕ}

def vfSchemaSource (A : Set (Point (M := M) p 0)) (F : GammaFiniteRVSchema B p a k) :
    Set (Point (M := M) p a) :=
  {z | (z.1,Fin.elim0) ∈ A ∧ z.2 ∈ F.rowDomain (rawVFParameter (z.1,Fin.elim0))}

theorem gamma_vf_schema_source_definable (A : Set (Point (M := M) p 0))
    (hA : GammaSetDefinable B A) (F : GammaFiniteRVSchema B p a k) :
    GammaSetDefinable B (vfSchemaSource A F) := by
  let g := mixedCoordinatePointMap (id : Fin p → Fin p) (Fin.elim0 : Fin 0 → Fin a) B.real
  have h := (gammaLogicInput B).inter (gamma_global_preimage g hA) F.toFamily.domain_definable
  convert h using 1
  apply Set.ext
  intro z
  change ((z.1,Fin.elim0) ∈ A ∧ _) ↔ ((z.1 ∘ id,z.2 ∘ Fin.elim0) ∈ A ∧ _)
  have he : (z.1 ∘ id,z.2 ∘ (Fin.elim0 : Fin 0 → Fin a)) = (z.1,Fin.elim0) :=
    Prod.ext rfl (Subsingleton.elim _ _)
  rw [he]
  exact and_congr Iff.rfl Iff.rfl

end IntegrationInACVF.Section6
