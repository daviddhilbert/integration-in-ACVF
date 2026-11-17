module

public import Integration7.HKAEZeroVolumeFunctions
public import Integration7.OrdinaryVolumeFamilyOutsideRows

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Removing a base exception keeps the same form on every remaining
point, and makes each removed row genuinely empty. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a b : ℕ}

def ZeroVFVolumeFamily.restrict (F : ZeroVFVolumeFamily C n a)
    (L : DefSet (rawMixedSpace (M := M) n a) (C.base : Set M))
    (hL : L.carrier ⊆ F.domain.carrier) : ZeroVFVolumeFamily C n a :=
  ⟨L,fun x => (F.finite_labels x).subset (fun _ hr => hL hr),F.form.restrict hL⟩

def ZeroVFVolumeFamily.outsideBase (F : ZeroVFVolumeFamily C n a)
    (E : DefSet (rawVFSpace (M := M) n) (C.base : Set M)) : ZeroVFVolumeFamily C n a :=
  F.restrict (F.toOrdinary.outsideBase E).domain Set.sdiff_subset

theorem zero_family_outside_base_mem (F : ZeroVFVolumeFamily C n a)
    (E : DefSet (rawVFSpace (M := M) n) (C.base : Set M))
    (q : (rawMixedSpace (M := M) n a).Carrier) :
    q ∈ (F.outsideBase E).domain.carrier ↔ q ∈ F.domain.carrier ∧ q.1 ∉ E.carrier :=
  ordinary_volume_family_outside_base_mem F.toOrdinary E q

def zeroFamilyOutsideBaseRowIso (F : ZeroVFVolumeFamily C n a)
    (E : DefSet (rawVFSpace (M := M) n) (C.base : Set M))
    (x : Fin n → VFType (M := M)) (hx : x ∉ E.carrier) :
    ZeroRVVolumeIso ((F.outsideBase E).rowInContext x) (F.rowInContext x) :=
  ⟨ordinaryFamilyOutsideBaseRowIso F.toOrdinary E x hx,fun _ => rfl⟩

theorem zero_family_outside_base_row_empty (F : ZeroVFVolumeFamily C n a)
    (E : DefSet (rawVFSpace (M := M) n) (C.base : Set M))
    (x : Fin n → VFType (M := M)) (hx : x ∈ E.carrier) :
    ((F.outsideBase E).rowInContext x).underlying.obj.domain.carrier = ∅ :=
  ordinary_family_outside_base_row_empty F.toOrdinary E x hx

theorem zero_family_full_class_outside_base
    (hc : CanonicalStructure.IsCanonical (M := M)) (F : ZeroVFVolumeFamily C (n+1) a)
    (E : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M))
    (hE : vfDim (rawRVSpace (M := M) 1) E < n+1) :
    positiveVFVolumeIsoClass hc C F.fullVFObject =
      positiveVFVolumeIsoClass hc C (F.outsideBase E).fullVFObject := by
  let L := (F.outsideBase E).domain
  have hL : VFCofull F.domain L := ⟨Set.sdiff_subset,
    (mixed_domain_vf_dim_le_base (F.domain.sdiff L) E (by
      intro q
      by_contra he
      exact q.property.2 ((zero_family_outside_base_mem F E q.val).mpr ⟨q.property.1,he⟩))).trans_lt hE⟩
  exact (positiveVFVolumeIsoClass_eq_iff hc C).mpr
    ⟨(vfVolumeCofullRestrictionIso hc C F.fullVFObject L hL).symm hc C⟩

theorem zero_outside_rows_eq_of_ae
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : ZeroVFVolumeFamily C (n+1) a) (G : ZeroVFVolumeFamily C (n+1) b)
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
    have hU := zero_family_outside_base_row_empty F E x hx
    have hV := zero_family_outside_base_row_empty G E x hx
    let f : Map U.underlying.obj.domain V.underlying.obj.domain := Map.fromEmpty hU V.underlying.obj.domain
    exact Quotient.sound ⟨ZeroRVVolumeIso.ofBijection f (Map.bijective_of_empty f hU hV)
      (fun u => (hU.le u.property).elim)⟩
  · exact (Quotient.sound (s := muIspSetoid hc (vfParameterVolumeContext C x) 0)
      ⟨zeroFamilyOutsideBaseRowIso F E x hx⟩).trans ((h x hx).trans
        (Quotient.sound (s := muIspSetoid hc (vfParameterVolumeContext C x) 0)
          ⟨zeroFamilyOutsideBaseRowIso G E x hx⟩).symm)

end IntegrationInACVF.Section7.HK
