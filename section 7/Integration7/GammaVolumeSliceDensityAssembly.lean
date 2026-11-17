module

public import Integration7.GammaVolumeSliceDensitySchemata
public import Integration7.GammaVolumeIndexedPresentations
public import Integration7.GammaVolumePresentationContexts
public import Integration7.CoordinateDensityVolumeObjects
public import Integration7.RVCoordinateSelection
public import Integration7.CanonicalFiniteRVObjects
public import IntegrationSection6.GammaIdentityIndexPresentation

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Reassembling all RV volume slices recovers the actual original
volume object. The label projection preserves the entire volume tuple
and the retained density, so it gives a genuine volume isomorphism. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open SpecialTransformations.Section7 (gammaVolumeValue)
open SpecialTransformations.Section5 (RV rvObjectArity rvObjectDomain GammaRVFiniteObject)
open SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {e k : ℕ}

def gammaCoordinateDensityObject
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : GammaRVFiniteObject B (e+(k+1))) (hUC : U.codes ⊆ (C.base : Set M))
    (δ : Fin (rvObjectArity U.object))
    (hNZ : ∀ u : rvObjectDomain U.object, (u.val δ).val ≠ iRVZero) :
    PositiveRVVolumeObject (M := M) (C.base : Set M) (e+k) :=
  coordinateDensityVolumeObject
    (canonicalFiniteRVObject hc (FiniteRV.gammaObjectAtExtend U hUC).object) δ
    (fun u => (rv_nonzero_iff_raw _).mpr (hNZ ⟨u.val,u.property⟩))

def gammaVolumeSliceDensityAssemblyIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : GammaRVFiniteObject B (e+(k+1))) (hUC : U.codes ⊆ (C.base : Set M))
    (δ : Fin (rvObjectArity U.object))
    (hNZ : ∀ u : rvObjectDomain U.object, (u.val δ).val ≠ iRVZero)
    (BP : IdentityIndexPresentation B e) (N : ℕ)
    (P : ((gammaVolumeSliceDensitySchema U δ).withBound N).IndexedPresentation BP)
    (hPC : P.finite.codes ⊆ (C.base : Set M)) :
    RVVolumeIso (P.inContext hc C hPC).toObject
      (gammaCoordinateDensityObject hc C U hUC δ hNZ) := by
  let F := (gammaVolumeSliceDensitySchema U δ).withBound N
  let A := (P.inContext hc C hPC).toObject
  let V := gammaCoordinateDensityObject hc C U hUC δ hNZ
  have hDom (w : A.underlying.obj.domain) :
      ∃ u : rvObjectDomain U.object, u.val = indexedRight w.val ∧
        gammaVolumeValue U.toGammaRVObject u ∘ Fin.castAdd (k+1) = indexedLeft w.val := by
    have hw := (Set.ext_iff.mp P.finite.domain_eq w.val).mp w.property
    exact (gammaVolumeSliceSchema_domain U (indexedLeft w.val) (indexedRight w.val)).mp hw.2
  let u (w : A.underlying.obj.domain) : rvObjectDomain U.object :=
    ⟨indexedRight w.val, by obtain ⟨v,hv,_⟩ := hDom w; exact hv ▸ v.property⟩
  have hPrefix (w : A.underlying.obj.domain) :
      gammaVolumeValue U.toGammaRVObject (u w) ∘ Fin.castAdd (k+1) = indexedLeft w.val := by
    obtain ⟨v,hv,hp⟩ := hDom w
    have he : v = u w := Subtype.ext hv
    exact he ▸ hp
  let f : Map A.underlying.obj.domain V.underlying.obj.domain :=
    ((rvCoordinateSelectMap (C.base : Set M) (Fin.natAdd e)).restrict
      (A' := A.underlying.obj.domain) (Set.subset_univ _)).corestrict (fun w => (u w).property)
  have hf : Function.Bijective f := by
    constructor
    · intro w v he
      have hr : indexedRight w.val = indexedRight v.val :=
        congrArg (fun z : V.underlying.obj.domain => z.val) he
      have hu : u w = u v := Subtype.ext hr
      have hl : indexedLeft w.val = indexedLeft v.val :=
        (hPrefix w).symm.trans ((congrArg
          (fun z => gammaVolumeValue U.toGammaRVObject z ∘ Fin.castAdd (k+1)) hu).trans (hPrefix v))
      apply Subtype.ext
      calc
        w.val = Fin.append (indexedLeft w.val) (indexedRight w.val) := Fin.append_castAdd_natAdd.symm
        _ = Fin.append (indexedLeft v.val) (indexedRight v.val) := congrArg₂ Fin.append hl hr
        _ = v.val := Fin.append_castAdd_natAdd
    · intro v
      let t := V.underlying.obj.value v ∘ Fin.castAdd (k+1)
      let w := Fin.append t v.val
      have hw : w ∈ A.underlying.obj.domain.carrier := by
        apply (Set.ext_iff.mp P.finite.domain_eq w).mpr
        refine ⟨Set.mem_univ _, ?_⟩
        have hl : indexedLeft w = t := funext (Fin.append_left _ _)
        have hr : indexedRight w = v.val := funext (Fin.append_right _ _)
        rw [hl,hr]
        exact (gammaVolumeSliceSchema_domain U t v.val).mpr ⟨⟨v.val,v.property⟩,rfl,rfl⟩
      exact ⟨⟨w,hw⟩, Subtype.ext (funext (Fin.append_right _ _))⟩
  have hcoord (w : A.underlying.obj.domain) :
      V.underlying.obj.value (f w) = A.underlying.obj.value w := by
    have hw := (P.finite.graph_iff w.val (A.underlying.obj.volume w).val).mp
      ⟨⟨w.val,w.property⟩,rfl,rfl⟩
    have hRow := gammaVolumeSliceSchema_value U (u w)
    have ht : (fun j => (gammaVolumeValue U.toGammaRVObject (u w) (Fin.castAdd (k+1) j)).val) =
        rvValues (indexedLeft w.val) := congrArg rvValues (hPrefix w)
    rw [ht] at hRow
    have hv := hw.2.2
    change Fin.append (BP.totalVolume (indexedLeft w.val)) (F.object.rowValue _ _) =
      A.underlying.obj.value w at hv
    change F.object.rowValue (rvValues (indexedLeft w.val)) (indexedRight w.val) = _ at hRow
    rw [BP.totalVolume_eq,hRow,← hPrefix w] at hv
    exact (show V.underlying.obj.value (f w) = gammaVolumeValue U.toGammaRVObject (u w) from rfl).trans
      (Fin.append_castAdd_natAdd.symm.trans hv)
  have hDensity (w : A.underlying.obj.domain) : V.form.value (f w) = A.form.value w := by
    have hw := (P.density_iff w.val (A.form.map w).val).mp ⟨⟨w.val,w.property⟩,rfl,rfl⟩
    have hr : (gammaVolumeSliceDensitySchema U δ).rowDensity
        (rvValues (indexedLeft w.val)) (indexedRight w.val) (A.form.map w).val := hw.2
    have h := (gammaVolumeSliceDensitySchema_row U δ hNZ _ _ _).mp hr
    exact h.2.symm
  exact RVVolumeIso.of_preserving_coordinates_full hc C
    (rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection f hf hcoord)) hcoord hDensity

end IntegrationInACVF.Section7
