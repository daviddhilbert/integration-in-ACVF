import Integration7.GammaRVVolumeSchemata
import IntegrationSection6.GammaSortedSchemaRows

/-! Exact typed density rows certify the full raw function-graph
validity, including rows at improper tuples. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open IntegrationInACVF.Section6
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a k : ℕ} {sp : Fin p → SortTag}

theorem GammaRVVolumeSchema.density_valid_of_typed (F : GammaRVVolumeSchema B p a k sp)
    (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i))
    (hUnique : ∀ x ∈ F.object.rowDomain z, ∃! y : Fin 1 → CanonicalRV.RVSort M, F.rowDensity z x y)
    (hSupport : ∀ x y, F.rowDensity z x y → x ∈ F.object.rowDomain z) :
    functionMapRowValid sp F.object.domain F.density z := by
  refine ⟨hz,?_,?_⟩
  · intro x hx
    obtain ⟨t,ht,rfl⟩ := (F.object.raw_row_domain_iff z x).mp hx
    obtain ⟨y,hy,hu⟩ := hUnique t ht
    refine ⟨rvValues y,hy,?_⟩
    intro y' hy'
    have hys (i : Fin 1) : iRV (y' i) := by
      simpa only [Fin.append_right,sortEval,iRV] using
        F.density_definable.proper _ hy' (Fin.natAdd (p+a) i)
    let s : Fin 1 → CanonicalRV.RVSort M := fun i => ⟨y' i,hys i⟩
    exact congrArg rvValues (hu s hy')
  · intro x y hxy
    have hxs (i : Fin a) : iRV (x i) := by
      simpa only [Fin.append_left,Fin.append_right,sortEval,iRV] using
        F.density_definable.proper _ hxy (Fin.castAdd 1 (Fin.natAdd p i))
    have hys (i : Fin 1) : iRV (y i) := by
      simpa only [Fin.append_right,sortEval,iRV] using
        F.density_definable.proper _ hxy (Fin.natAdd (p+a) i)
    exact hSupport (fun i => ⟨x i,hxs i⟩) (fun i => ⟨y i,hys i⟩) hxy

end IntegrationInACVF.Section7
