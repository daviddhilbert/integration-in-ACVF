import IntegrationSection6.FullFocusBlowup
import IntegrationSection6.VolumePreservingLift

/-! The RV-image isomorphism in6.9 preserves the full volume tuple.
Its lift is the explicit VF-coordinate-preserving relabeling in6.12. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.rawVFSpace SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.rawMixedSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace IntegrationInACVF.Section6
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n : ℕ}

theorem elementaryKeyIso_hom_volume (U : RVObject (M := M) S n) (i : Fin n)
    (h : Admissible U i) (a : (elementary U i).domain) :
    (elementaryKeyObject U i).value ((elementaryKeyIso U i h).hom.map a) =
      (elementary U i).value a := by
  funext j
  change rvAppend ((elementary U i).value a) (elementaryProjection U i a).val
    (Fin.castAdd U.arity j) = _
  exact Fin.append_left _ _ j

theorem elementaryKeyIso_inv_volume (U : RVObject (M := M) S n) (i : Fin n)
    (h : Admissible U i) (a : (elementaryKeyObject U i).domain) :
    (elementary U i).value ((elementaryKeyIso U i h).inv.map a) =
      (elementaryKeyObject U i).value a := by
  have hv := elementaryKeyIso_hom_volume U i h ((elementaryKeyIso U i h).inv.map a)
  rw [iso_inv_hom_apply] at hv
  exact hv.symm

variable {U : RVObject (M := M) S n}
variable {A : SpecialTransformations.Section5.DefSet (M := M) S n U.arity}
variable (h : PresentsLift U A) {i : Fin n} {k : Fin U.arity}
variable (D : SpecialTransformations.Section5.Focus A i k)
variable (hfull : SpecialTransformations.Section5.carrier A ⊆ D.locus)
variable (hnz : ∀ u : U.domain, U.value u i ≠ 0)

theorem fullFocusBlowup_iso_volume {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (a : (fullFocusObject h D hfull hnz).domain) :
    (elementary U i).value ((lemma_6_9 h D hfull hnz hκ hs hsmall).iso.hom.map a) =
      (fullFocusObject h D hfull hnz).value a := by
  let E := lemma_6_9 h D hfull hnz hκ hs hsmall
  change (elementary U i).value ((elementaryKeyIso U i E.admissible).inv.map
    ((fullFocusObjectKeyIso h D hfull hnz).hom.map a)) = _
  exact elementaryKeyIso_inv_volume U i E.admissible
    ((fullFocusObjectKeyIso h D hfull hnz).hom.map a)

/-- The complete graph is definable and every VF coordinate is fixed. -/
def fullFocusRelabelLift {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ) :=
  volumePreservingLiftMap (lemma_6_9 h D hfull hnz hκ hs hsmall).iso.hom.map
    (fullFocusBlowup_iso_volume h D hfull hnz hκ hs hsmall)

theorem fullFocusRelabelLift_bijective {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ) :
    Function.Bijective (fullFocusRelabelLift h D hfull hnz hκ hs hsmall) :=
  volumePreservingLiftMap_bijective _ _
    (iso_map_bijective (lemma_6_9 h D hfull hnz hκ hs hsmall).iso)

@[simp] theorem fullFocusRelabelLift_vf {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (a : rvLift (fullFocusObject h D hfull hnz)) :
    (fullFocusRelabelLift h D hfull hnz hκ hs hsmall a).val.1 = a.val.1 := rfl

@[simp] theorem fullFocusRelabelLift_square {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (a : rvLift (fullFocusObject h D hfull hnz)) :
    (fullFocusRelabelLift h D hfull hnz hκ hs hsmall a).val.2 =
      ((lemma_6_9 h D hfull hnz hκ hs hsmall).iso.hom.map
        (liftLabelProjection (fullFocusObject h D hfull hnz) a)).val := rfl

end IntegrationInACVF.Section6
