import IntegrationSection6.GammaVolumeSliceSchemata
import IntegrationSection6.GammaIdentityIndexPresentation
import IntegrationSection6.GammaSchemaIndexedPresentations

/-! Reassembling all volume slices over the identity RV[e] index recovers
the original RV[e+k] object by a full Gamma isomorphism. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {e k : ℕ}

def gammaVolumeSliceAssemblyIso (U : GammaRVFiniteObject B (e+k)) (BP : IdentityIndexPresentation B e)
    (P : (gammaVolumeSliceSchema U).IndexedPresentation BP) :
    GammaRVIso P.toGamma.toGammaRVObject U.toGammaRVObject := by
  let F := gammaVolumeSliceSchema U
  have hDom (w : P.domain) :
      ∃ u : rvObjectDomain U.object, u.val = indexedRight w.val ∧
        gammaVolumeValue U.toGammaRVObject u ∘ Fin.castAdd k = indexedLeft w.val := by
    have hw := (Set.ext_iff.mp P.domain_eq w.val).mp w.property
    exact (gammaVolumeSliceSchema_domain U (indexedLeft w.val) (indexedRight w.val)).mp hw.2
  let f (w : P.domain) : rvObjectDomain U.object :=
    ⟨indexedRight w.val,by obtain ⟨u,hu,_⟩ := hDom w; exact hu ▸ u.property⟩
  have hPrefix (w : P.domain) : gammaVolumeValue U.toGammaRVObject (f w) ∘ Fin.castAdd k = indexedLeft w.val := by
    obtain ⟨u,hu,hv⟩ := hDom w
    have he : u = f w := Subtype.ext hu
    exact he ▸ hv
  have hVol (w : P.domain) : (P.volume w).val = gammaVolumeValue U.toGammaRVObject (f w) := by
    have hw := (P.graph_iff w.val (P.volume w).val).mp ⟨w,rfl,rfl⟩
    have hW := (F.rowValue_graph_of_finiteRow _ (gammaVolumeSliceSchema_finiteRows U (indexedLeft w.val))
      (indexedRight w.val) hw.1.2 (gammaVolumeValue U.toGammaRVObject (f w) ∘ Fin.natAdd e)).mp
      ((gammaVolumeSliceSchema_volume U _ _ _).mpr ⟨f w,rfl,by
        rw [← hPrefix w]; exact Fin.append_castAdd_natAdd.symm⟩)
    have hv := hw.2.2
    change Fin.append (BP.totalVolume (indexedLeft w.val)) (F.rowValue _ _) = (P.volume w).val at hv
    rw [BP.totalVolume_eq,hW,← hPrefix w] at hv
    exact hv.symm.trans Fin.append_castAdd_natAdd
  have hf : Function.Bijective f := by
    constructor
    · intro w v he
      have hr : indexedRight w.val = indexedRight v.val := congrArg Subtype.val he
      have hl : indexedLeft w.val = indexedLeft v.val :=
        (hPrefix w).symm.trans ((congrArg (fun u => gammaVolumeValue U.toGammaRVObject u ∘ Fin.castAdd k) he).trans (hPrefix v))
      apply Subtype.ext
      calc
        w.val = Fin.append (indexedLeft w.val) (indexedRight w.val) := Fin.append_castAdd_natAdd.symm
        _ = Fin.append (indexedLeft v.val) (indexedRight v.val) := congrArg₂ Fin.append hl hr
        _ = v.val := Fin.append_castAdd_natAdd
    · intro u
      let t := gammaVolumeValue U.toGammaRVObject u ∘ Fin.castAdd k
      let w := Fin.append t u.val
      have hw : w ∈ indexedDomain Set.univ (fun t => F.rowDomain (fun j => (t j).val)) := by
        refine ⟨Set.mem_univ _,?_⟩
        have hl : indexedLeft w = t := funext (fun j => Fin.append_left _ _ j)
        have hr : indexedRight w = u.val := funext (fun j => Fin.append_right _ _ j)
        rw [hl,hr]
        exact (gammaVolumeSliceSchema_domain U t u.val).mpr ⟨u,rfl,rfl⟩
      let v := P.domainEquiv.symm ⟨w,hw⟩
      refine ⟨v,Subtype.ext ?_⟩
      change indexedRight w = u.val
      exact funext (fun j => Fin.append_right _ _ j)
  refine FiniteRV.gammaIsoOfFiniteEquiv P.toGamma U (Equiv.ofBijective f hf) ?_ ?_
  · let g := rvCoordinatePointMap (Fin.natAdd e : Fin (rvObjectArity U.object) → Fin (e+rvObjectArity U.object)) B.real
    have h := (gammaLogicInput B).restrict_graph P.domain_graph ((gammaLogicInput B).real_map_graph g)
    apply GammaGraphDefinable.congr h
    intro p q
    constructor
    · rintro ⟨hp,z,hz,hq⟩
      let w : P.domain := ⟨p.2,(Set.ext_iff.mp P.domain_eq p.2).mpr hp⟩
      refine ⟨w,rfl,?_⟩
      change indexedRight p.2 = q.2
      have he := congrArg Prod.snd hq
      have hz' := congrArg Prod.snd hz
      exact (congrArg (fun v => indexedRight v) hz').symm.trans he
    · rintro ⟨w,hw,hq⟩
      have hpD : p.2 ∈ indexedDomain Set.univ (fun t => F.rowDomain (fun j => (t j).val)) :=
        hw ▸ (Set.ext_iff.mp P.domain_eq w.val).mp w.property
      refine ⟨hpD,⟨p,Set.mem_univ _⟩,rfl,?_⟩
      apply Prod.ext (Subsingleton.elim _ _)
      change indexedRight p.2 = q.2
      exact (congrArg (fun v => indexedRight v) hw).symm.trans hq
  · intro w
    exact congrArg (fun v : Fin (e+k) → RV (M := M) => rawWeight (fun j => (v j).val)) (hVol w)

end IntegrationInACVF.Section6
