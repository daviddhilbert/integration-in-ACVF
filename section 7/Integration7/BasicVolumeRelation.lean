module

public import Integration7.BasicVolumeRelationObjects
public import Integration7.VolumeBlowupEquivalence
public import Integration7.VolumeCoproductUnits
public import Section4.RVIsoTools

@[expose] public section

/-! The degree-one point and open RV cone satisfy the actual common
volume blowup relation, using their concrete unit-density objects. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

def VolumeBlowup.ofElementary
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k} (b : ElementaryBlowup U V) :
    VolumeBlowup U V where
  locus := U
  complement := .empty (C.base : Set M) k
  blownLocus := V
  elementary := b
  sourceIso := (volumeCoprodRightUnit hc C U).symm hc C
  targetIso := (volumeCoprodRightUnit hc C V).symm hc C

def degreeOneBasicElementaryIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
    RVVolumeIso
      (elementaryVolumeObject C (degreeOnePointVolumeObject (C.base : Set M))
        (degreeOnePointAdmissible hc (C.base : Set M)))
      (degreeOneConeVolumeObject (C.base : Set M)) := by
  let U := degreeOnePointVolumeObject (M := M) (C.base : Set M)
  let V := degreeOneConeVolumeObject (M := M) (C.base : Set M)
  let b := elementaryVolumeBlowup C U (degreeOnePointAdmissible hc (C.base : Set M))
  let W := elementaryVolumeObject C U (degreeOnePointAdmissible hc (C.base : Set M))
  let f : Map W.underlying.obj.domain V.underlying.obj.domain := b.parameter
  have hf : Function.Bijective f := by
    constructor
    · intro u v huv
      apply b.chartMap_bijective.1
      apply Subtype.ext
      apply Prod.ext
      · funext i
        exact Fin.elim0 i
      · exact congrArg Subtype.val huv
    · intro s
      let u : U.underlying.obj.domain := ⟨Fin.elim0,Set.mem_univ _⟩
      obtain ⟨w,hw⟩ := b.chartMap_bijective.2 ⟨(u.val,s.val),u.property,s.property⟩
      exact ⟨w,congrArg (Map.prodSnd U.underlying.obj.domain (blowupConeSet (C.base : Set M))) hw⟩
  have hCoord (w : W.underlying.obj.domain) : V.underlying.obj.value (f w) = W.underlying.obj.value w := by
    funext i
    have hi : i = (0 : Fin 1) := Fin.fin_one_eq_zero i
    subst i
    have h := b.last w
    change W.underlying.obj.value w 0 = (f w).val (0 : Fin 1) * 1 at h
    rw [mul_one] at h
    exact h.symm
  let e : W.underlying ≅ V.underlying := rvFiniteIsoOfAmbient
    (U := W.underlying) (V := V.underlying) (rvIsoOfVolumePreservingBijection f hf hCoord)
  exact RVVolumeIso.of_preserving_coordinates_full hc C e hCoord (fun _ => rfl)

theorem degree_one_basic_volume_relation
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
    VolumeBlowupEquivalent (degreeOnePointVolumeObject (M := M) (C.base : Set M))
      (degreeOneConeVolumeObject (M := M) (C.base : Set M)) :=
  (VolumeBlowupEquivalent.of_blowup hc C (VolumeBlowup.ofElementary hc C
    (elementaryVolumeBlowup C _ (degreeOnePointAdmissible hc (C.base : Set M))))).trans hc C
      (VolumeBlowupEquivalent.of_iso C (degreeOneBasicElementaryIso hc C))

end IntegrationInACVF.Section7
