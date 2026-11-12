import IntegrationSection6.GammaRVFamilyFormulas

/-! Literal rows of the mixed-point family interface at an actual VF
tuple. Raw schemas and typed rows have the same domains and volumes. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a k : ℕ}

def GammaRVFamilyFormula.rowDomain (F : GammaRVFamilyFormula B p a k) (z : Fin p → VF (M := M)) :
    Set (Fin a → RV (M := M)) := {x | (z,x) ∈ F.domain}

def GammaRVFamilyFormula.rowVolume (F : GammaRVFamilyFormula B p a k) (z : Fin p → VF (M := M))
    (x : Fin a → RV (M := M)) (y : Fin k → RV (M := M)) : Prop := F.volume (z,x) (Fin.elim0,y)

theorem GammaRVFamilyFormula.schema_row_domain (F : GammaRVFamilyFormula B p a k) (N : ℕ)
    (z : Fin p → VF (M := M)) :
    (F.schema N).rowDomain (fun j => (z j).val) = F.rowDomain z := by
  apply Set.ext
  intro x
  change gammaPointCode (z,x) ∈ (F.schema N).domain ↔ (z,x) ∈ F.domain
  exact F.schema_domain N (z,x)

theorem GammaRVFamilyFormula.schema_row_volume (F : GammaRVFamilyFormula B p a k) (N : ℕ)
    (z : Fin p → VF (M := M)) (x : Fin a → RV (M := M)) (y : Fin k → RV (M := M)) :
    (F.schema N).rowVolume (fun j => (z j).val) x y ↔ F.rowVolume z x y :=
  F.schema_volume N (z,x) (Fin.elim0,y)

theorem GammaFiniteRVSchema.toFamily_row_domain (F : GammaFiniteRVSchema B p a k)
    (z : Fin p → VF (M := M)) : F.toFamily.rowDomain z = F.rowDomain (fun j => (z j).val) := rfl

theorem GammaFiniteRVSchema.toFamily_row_volume (F : GammaFiniteRVSchema B p a k)
    (z : Fin p → VF (M := M)) (x : Fin a → RV (M := M)) (y : Fin k → RV (M := M)) :
    F.toFamily.rowVolume z x y ↔ F.rowVolume (fun j => (z j).val) x y := Iff.rfl

end IntegrationInACVF.Section6
