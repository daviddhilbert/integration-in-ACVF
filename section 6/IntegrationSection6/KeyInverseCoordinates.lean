import IntegrationSection6.VolumePreservingElementary
import IntegrationSection6.AdmissibleFocusRelabeling

/-! Coordinate identities for inverses of the actual RV key isomorphisms. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n : ℕ}

theorem canonicalRVKeyIso_inv_labels (U : RVObject (M := M) S n)
    (a : (canonicalRVKeyObject U).domain) :
    ((canonicalRVKeyIso U).inv.map a).val = fun j => a.val (Fin.natAdd n j) := by
  have he := congrArg (fun b : (canonicalRVKeyObject U).domain => b.val)
    (iso_inv_hom_apply (canonicalRVKeyIso U) a)
  change rvAppend (U.value ((canonicalRVKeyIso U).inv.map a))
    ((canonicalRVKeyIso U).inv.map a).val = a.val at he
  funext j
  exact (Fin.append_right _ _ j).symm.trans (congrFun he (Fin.natAdd n j))

theorem elementaryKeyIso_inv_key (U : RVObject (M := M) S n) (i : Fin n)
    (hAd : Admissible U i) (a : (elementaryKeyObject U i).domain) :
    rvAppend ((elementary U i).value ((elementaryKeyIso U i hAd).inv.map a))
      (elementaryProjection U i ((elementaryKeyIso U i hAd).inv.map a)).val = a.val :=
  congrArg (fun b : (elementaryKeyObject U i).domain => b.val)
    (iso_inv_hom_apply (elementaryKeyIso U i hAd) a)

theorem elementaryKeyIso_inv_labels (U : RVObject (M := M) S n) (i : Fin n)
    (hAd : Admissible U i) (a : (elementaryKeyObject U i).domain) :
    (elementaryProjection U i ((elementaryKeyIso U i hAd).inv.map a)).val =
      fun j => a.val (Fin.natAdd n j) := by
  have he := elementaryKeyIso_inv_key U i hAd a
  funext j
  exact (Fin.append_right _ _ j).symm.trans (congrFun he (Fin.natAdd n j))

theorem elementaryKeyIso_inv_parameter (U : RVObject (M := M) S n) (i : Fin n)
    (hAd : Admissible U i) (a : (elementaryKeyObject U i).domain) :
    (elementaryParameter U i ((elementaryKeyIso U i hAd).inv.map a)).val 0 =
      a.val (Fin.castAdd U.arity i) /
        U.value (elementaryProjection U i ((elementaryKeyIso U i hAd).inv.map a)) i := by
  have he := congrFun (elementaryKeyIso_inv_key U i hAd a) (Fin.castAdd U.arity i)
  simp only [rvAppend,Fin.append_left] at he
  rw [elementary_value,blowupValue_same] at he
  exact (eq_div_iff (hAd.rv_nonzero _)).mpr he

theorem elementary_labels (U : RVObject (M := M) S n) (i : Fin n)
    (a : (elementary U i).domain) :
    a.val = rvAppend (elementaryProjection U i a).val (elementaryParameter U i a).val := by
  obtain ⟨u,s,rfl⟩ := exists_rvPackPair U.domain (positiveRV S) a
  rw [elementaryProjection_pair,elementaryParameter_pair]
  rfl

theorem canonicalElementaryIso_labels (U : RVObject (M := M) S n) (i : Fin n)
    (a : (elementary (canonicalRVKeyObject U) i).domain) :
    ((canonicalElementaryIso U i).hom.map a).val =
      rvAppend (fun j => (elementaryProjection (canonicalRVKeyObject U) i a).val (Fin.natAdd n j))
        (elementaryParameter (canonicalRVKeyObject U) i a).val := by
  change (elementaryMap i i (canonicalRVKeyIso U).inv.map a).val = _
  rw [elementary_labels U i,elementaryMap_projection,elementaryMap_parameter,
    canonicalRVKeyIso_inv_labels]

end IntegrationInACVF.Section6
