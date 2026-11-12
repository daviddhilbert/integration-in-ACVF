import IntegrationSection6.GammaVolumeSliceEmbeddings
import IntegrationSection6.FiniteGammaIsoLaws

/-! Exact volume-preserving original-Gamma RV isomorphisms restrict to
isomorphisms of all volume slices, for arbitrary actual presentations. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {e k : ℕ}
variable {U V : GammaRVFiniteObject B (e+k)}
variable (f : GammaRVIso U.toGammaRVObject V.toGammaRVObject)
variable (hf : ∀ u, gammaVolumeValue V.toGammaRVObject (f.equiv u) = gammaVolumeValue U.toGammaRVObject u)
variable (t : Fin e → RV (M := M))
variable (P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (fun j => (t j).val),B.gamma⟩
  (rvObjectArity U.object) k ((gammaVolumeSliceSchema U).rowDomain (fun j => (t j).val))
  ((gammaVolumeSliceSchema U).rowVolume (fun j => (t j).val)))
variable (Q : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (fun j => (t j).val),B.gamma⟩
  (rvObjectArity V.object) k ((gammaVolumeSliceSchema V).rowDomain (fun j => (t j).val))
  ((gammaVolumeSliceSchema V).rowVolume (fun j => (t j).val)))

def volumeSliceIsoMap (u : P.domain) : Q.domain :=
  ⟨(f.equiv (volumeSliceUnderlying U t P u)).val,
    (volumeSlicePresentation_mem V t Q _).mpr ⟨_,rfl,by
      rw [hf]
      exact volumeSliceUnderlying_prefix U t P u⟩⟩

theorem volumeSliceIsoMap_bijective : Function.Bijective (volumeSliceIsoMap f hf t P Q) := by
  constructor
  · intro u v he
    have h := f.equiv.injective (Subtype.ext (congrArg (fun q : Q.domain => q.val) he))
    exact Subtype.ext (congrArg (fun q : rvObjectDomain U.object => q.val) h)
  · intro v
    let b := volumeSliceUnderlying V t Q v
    let a := f.equiv.symm b
    have ha : gammaVolumeValue U.toGammaRVObject a ∘ Fin.castAdd k = t := by
      have h := hf a
      rw [Equiv.apply_symm_apply] at h
      exact (congrArg (fun z => z ∘ Fin.castAdd k) h).symm.trans (volumeSliceUnderlying_prefix V t Q v)
    let u : P.domain := ⟨a.val,(volumeSlicePresentation_mem U t P _).mpr ⟨a,rfl,ha⟩⟩
    refine ⟨u,Subtype.ext ?_⟩
    change (f.equiv (volumeSliceUnderlying U t P u)).val = v.val
    have he : volumeSliceUnderlying U t P u = a := Subtype.ext rfl
    rw [he]
    exact congrArg (fun z : rvObjectDomain V.object => z.val) (f.equiv.apply_symm_apply b)

def gammaVolumeSliceIso : GammaRVIso P.toGamma.toGammaRVObject Q.toGamma.toGammaRVObject := by
  let F := volumeSliceIsoMap f hf t P Q
  apply gammaIsoOfFiniteEquiv P.toGamma Q.toGamma
    (Equiv.ofBijective F (volumeSliceIsoMap_bijective f hf t P Q))
  · apply GammaGraphDefinable.congr ((gammaLogicInput _).restrict_graph P.toGamma.domain_graph
      (f.graph.mono Set.subset_union_left (Set.Subset.refl _)))
    intro p q
    constructor
    · rintro ⟨hp,u,hu,hq⟩
      let a : P.domain := ⟨p.2,hp⟩
      have he : volumeSliceUnderlying U t P a = u := Subtype.ext hu.symm
      exact ⟨a,rfl,(congrArg (fun z => (f.equiv z).val) he).trans hq⟩
    · rintro ⟨a,ha,hq⟩
      have hp : p.2 ∈ carrier P.domain := ha ▸ a.property
      exact ⟨hp,volumeSliceUnderlying U t P a,ha,hq⟩
  · intro u
    have he : volumeSliceUnderlying V t Q (F u) = f.equiv (volumeSliceUnderlying U t P u) := Subtype.ext rfl
    have hv : (Q.volume (F u)).val = (P.volume u).val := by
      rw [volumeSlicePresentation_volume V t Q,he,hf,← volumeSlicePresentation_volume U t P]
    exact congrArg (fun z : Fin k → RV (M := M) => rawWeight (fun j => (z j).val)) hv.symm

end IntegrationInACVF.Section6.FiniteRV
