module

public import Integration7.ElementaryBlowupConstruction
public import Integration7.GradedVolumeProducts
public import Integration7.TermClosureDefinability
public import Section3.VFDefinableClosure
public import IntegrationSection6.FiniteGammaBasicFactors

@[expose] public section

/-! The actual degree-one point and open RV cone, with unit densities.
The point is admissible over every base, with no named RV-unit premise. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

def degreeOnePointVolumeObject (S : Set M) : PositiveRVVolumeObject (M := M) S 0 :=
  ⟨Section6.FiniteRV.oneVolumeRVObject S,VolumeForm.one _⟩

def degreeOneConeVolumeObject (S : Set M) : PositiveRVVolumeObject (M := M) S 0 :=
  ⟨Section6.FiniteRV.positiveVolumeRVObject S,VolumeForm.one _⟩

theorem degree_one_point_volume_coordinates (u : (degreeOnePointVolumeObject (M := M) S).underlying.obj.domain) :
    (degreeOnePointVolumeObject (M := M) S).underlying.obj.value u = fun _ => 1 := rfl

theorem degreeOnePointAdmissible (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) :
    BlowupAdmissible (degreeOnePointVolumeObject (M := M) S) where
  nonzero _ := one_ne_zero
  algebraic u := by
    let A := Section6.coordinateBase S (Fin.last 0)
      ((degreeOnePointVolumeObject (M := M) S).underlying.obj.value u)
    change AlgebraicAt A .rv (1 : CanonicalRV.RVSort M).val
    rw [RVOperations.one_val]
    have hraw : A.Definable₁ LRV {iRVOne (M := M)} :=
      SpecialTransformations.DefinableConstants.function_symbol (L := LRV) (M := M) (A := A)
        Fn.rvOne Fin.elim0 (fun i => i.elim0)
    exact ((definableClosureAt_iff_raw hc A .rv _).mpr
      ⟨hraw,SpecialTransformations.Milestone0.Transfer.rv_one_mem inferInstance⟩).algebraic

end IntegrationInACVF.Section7
