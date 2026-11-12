import IntegrationSection6.GammaVolumeSliceSchemata

/-! Literal underlying labels and volumes of arbitrary actual presentations
of a volume slice. No chosen presentation is assumed canonical. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {e k : ℕ}
variable (U : GammaRVFiniteObject B (e+k)) (t : Fin e → RV (M := M))
variable (P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (fun j => (t j).val),B.gamma⟩
  (rvObjectArity U.object) k
  ((gammaVolumeSliceSchema U).rowDomain (fun j => (t j).val))
  ((gammaVolumeSliceSchema U).rowVolume (fun j => (t j).val)))

theorem volumeSlicePresentation_mem (x : Fin (rvObjectArity U.object) → RV (M := M)) :
    x ∈ carrier P.domain ↔ ∃ u : rvObjectDomain U.object, u.val = x ∧
      gammaVolumeValue U.toGammaRVObject u ∘ Fin.castAdd k = t := by
  exact (Set.ext_iff.mp P.domain_eq x).trans (gammaVolumeSliceSchema_domain U t x)

def volumeSliceUnderlying (u : P.domain) : rvObjectDomain U.object :=
  ⟨u.val,by
    obtain ⟨v,hv,_⟩ := (volumeSlicePresentation_mem U t P u.val).mp u.property
    exact hv ▸ v.property⟩

theorem volumeSliceUnderlying_prefix (u : P.domain) :
    gammaVolumeValue U.toGammaRVObject (volumeSliceUnderlying U t P u) ∘ Fin.castAdd k = t := by
  obtain ⟨v,hv,ht⟩ := (volumeSlicePresentation_mem U t P u.val).mp u.property
  have he : v = volumeSliceUnderlying U t P u := Subtype.ext hv
  exact he ▸ ht

theorem volumeSlicePresentation_volume (u : P.domain) :
    (P.volume u).val = gammaVolumeValue U.toGammaRVObject (volumeSliceUnderlying U t P u) ∘ Fin.natAdd e := by
  have h := (P.graph_iff u.val (P.volume u).val).mp ⟨u,rfl,rfl⟩
  obtain ⟨v,hv,hvol⟩ := (gammaVolumeSliceSchema_volume U t u.val _).mp h.2
  have he : v = volumeSliceUnderlying U t P u := Subtype.ext hv
  rw [he] at hvol
  funext j
  exact (Fin.append_right t (P.volume u).val j).symm.trans (congrFun hvol (Fin.natAdd e j)).symm

end IntegrationInACVF.Section6
