module

public import Integration7.OrdinaryVolumeFamilyRestrictions
public import Integration7.AEOrdinaryRVVolumeFunctions
public import Integration7.NondegenerateFiniteIso
public import Section4.EmptyMaps

@[expose] public section

/-! On ordinary rows, removing a base exception preserves every good
fibre and makes every bad fibre literally empty. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a b : ℕ}

def ordinaryFamilyOutsideBaseRowIso (F : OrdinaryVFVolumeFamily C n a)
    (E : DefSet (rawVFSpace (M := M) n) (C.base : Set M))
    (x : Fin n → VFType (M := M)) (hx : x ∉ E.carrier) :
    (F.outsideBase E).rowInContext x ≅ F.rowInContext x := by
  let f : Map ((F.outsideBase E).rowInContext x).obj.domain (F.rowInContext x).obj.domain :=
    Map.inclusion (fun r hr => ((ordinary_volume_family_outside_base_mem F E (x,r)).mp hr).1)
  have hf : Function.Bijective f := by
    refine ⟨?_,?_⟩
    · intro u v h
      have he := congrArg (fun z : (F.rowInContext x).obj.domain => z.val) h
      exact Subtype.ext he
    intro u
    exact ⟨⟨u.val,(ordinary_volume_family_outside_base_mem F E (x,u.val)).mpr ⟨u.property,hx⟩⟩,rfl⟩
  exact finiteIsoOfNondegenerateBijection f hf (fun _ i => i.elim0) (fun _ i => i.elim0)

theorem ordinary_family_outside_base_row_empty (F : OrdinaryVFVolumeFamily C n a)
    (E : DefSet (rawVFSpace (M := M) n) (C.base : Set M))
    (x : Fin n → VFType (M := M)) (hx : x ∈ E.carrier) :
    ((F.outsideBase E).rowInContext x).obj.domain.carrier=∅ := by
  ext r
  constructor
  · intro hr
    exact (((ordinary_volume_family_outside_base_mem F E (x,r)).mp hr).2 hx).elim
  · intro hr
    exact hr.elim

theorem ordinary_outside_rows_eq_of_ae
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : OrdinaryVFVolumeFamily C (n+1) a) (G : OrdinaryVFVolumeFamily C (n+1) b)
    (E : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M))
    (h : ∀ x, x ∉ E.carrier →
      rvVolumeBlowupClass hc (vfParameterVolumeContext C x) (n := 0) (F.rowInContext x) =
        rvVolumeBlowupClass hc (vfParameterVolumeContext C x) (n := 0) (G.rowInContext x)) :
    ∀ x, rvVolumeBlowupClass hc (vfParameterVolumeContext C x) (n := 0) ((F.outsideBase E).rowInContext x) =
      rvVolumeBlowupClass hc (vfParameterVolumeContext C x) (n := 0) ((G.outsideBase E).rowInContext x) := by
  classical
  intro x
  by_cases hx : x ∈ E.carrier
  · let U := (F.outsideBase E).rowInContext x
    let V := (G.outsideBase E).rowInContext x
    have hU := ordinary_family_outside_base_row_empty F E x hx
    have hV := ordinary_family_outside_base_row_empty G E x hx
    let f : Map U.obj.domain V.obj.domain := Map.fromEmpty hU V.obj.domain
    exact Quotient.sound ⟨finiteIsoOfNondegenerateBijection f (Map.bijective_of_empty f hU hV)
      (fun _ i => i.elim0) (fun _ i => i.elim0)⟩
  · exact (Quotient.sound (s := muIspSetoid hc (vfParameterVolumeContext C x) 0)
      ⟨ordinaryFamilyOutsideBaseRowIso F E x hx⟩).trans ((h x hx).trans
        (Quotient.sound (s := muIspSetoid hc (vfParameterVolumeContext C x) 0)
          ⟨ordinaryFamilyOutsideBaseRowIso G E x hx⟩).symm)

end IntegrationInACVF.Section7
