import IntegrationSection6.GammaPureVFBaseExtensions
import IntegrationSection6.GammaIsoSourceImages
import IntegrationSection6.GammaVFSchemaSources
import IntegrationSection6.PreparedKeyExtensionMaps

/-! Change the actual VF base of a mixed RV family by a Gamma isomorphism
and then attach its full prepared key, preserving all fibre RV labels. -/
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
variable {B : Base (M := M)} {p l a k : ℕ}
variable {A : Set (Point (M := M) p 0)} {C : Set (Point (M := M) p l)}

theorem vfSchemaSource_subset_extension (F : GammaFiniteRVSchema B p a k) :
    vfSchemaSource A F ⊆ pureVFExtension A a := by
  exact fun _ hz => hz.1

def vfBaseChangedFamily (e : GammaIso B A C) (F : GammaFiniteRVSchema B p a k) : Set (Point (M := M) p (l+a)) :=
  {q | ∃ z : vfSchemaSource A F,
    ((gammaIsoVFAppendRV e a).equiv ⟨z.val,vfSchemaSource_subset_extension F z.property⟩).val = q}

def gammaVFBaseChangeIso (e : GammaIso B A C) (hA : GammaSetDefinable B A)
    (F : GammaFiniteRVSchema B p a k) : GammaIso B (vfSchemaSource A F) (vfBaseChangedFamily e F) :=
  gammaIsoSourceImage (gammaIsoVFAppendRV e a) (vfSchemaSource A F)
    (vfSchemaSource_subset_extension F) (gamma_vf_schema_source_definable A hA F)

def preparedFamilyImage (e : GammaIso B A C) (F : GammaFiniteRVSchema B p a k) :
    Set (Point (M := M) p ((p+l)+a)) :=
  {q | ∃ z : vfBaseChangedFamily e F,
    (preparedKeyExtensionMap B.real p l a ⟨z.val,Set.mem_univ _⟩).val = q}

def gammaPreparedFamilyIso (e : GammaIso B A C) (hA : GammaSetDefinable B A)
    (F : GammaFiniteRVSchema B p a k) : GammaIso B (vfSchemaSource A F) (preparedFamilyImage e F) := by
  let f := gammaVFBaseChangeIso e hA F
  let g := gammaIso_realImage (vfBaseChangedFamily e F) (f.target_definable (gammaLogicInput B))
    (preparedKeyExtensionMap B.real p l a) (preparedKeyExtensionMap_injective B.real)
  exact f.trans (gammaLogicInput B) g

end IntegrationInACVF.Section6
