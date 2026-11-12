import IntegrationSection6.RawSelectedSliceCarriers
import IntegrationSection6.RestrictedStandardContractionData
import IntegrationSection6.RawFiniteContractions

/-! A raw volume slice is actually isomorphic to the finite contraction
of the corresponding RV-label slice of the original mixed set. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n a k : ℕ}
variable {U : DefSet (M := M) Set.univ n a} {σ : Equiv.Perm (Fin n)}
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (hreal : Cardinal.mk B.real < κ)
variable (hU : GammaSetDefinable B (carrier U)) (ρ : Fin k → Fin a)
variable (hfin : ∀ (x : Fin n → VF (M := M)) (t : Fin k → RV (M := M)),
  {r : Fin a → RV (M := M) | (x,r) ∈ carrier U ∧ r ∘ ρ = t}.Finite)
variable (C : StandardContraction U σ) (hC : GammaProgramDefinable B C.program)
variable (t : Fin k → RV (M := M))
variable (D : RestrictedStandardData C hU hC ρ t)
variable (P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (fun j => (t j).val),B.gamma⟩ C.arity n
  ((gammaVolumeSliceSchema (gammaSwapVolumeBlocks (gammaRawSelectedContraction hκ hs hreal (Set.subset_univ _) hU ρ hfin C hC))).rowDomain (fun j => (t j).val))
  ((gammaVolumeSliceSchema (gammaSwapVolumeBlocks (gammaRawSelectedContraction hκ hs hreal (Set.subset_univ _) hU ρ hfin C hC))).rowVolume (fun j => (t j).val)))

theorem rawSelectedSlice_restricted_domain (r : Fin C.arity → RV (M := M)) :
    r ∈ carrier P.domain ↔ r ∈ carrier (rvObjectDomain D.contraction.contractionObject) :=
  (rawSelectedSlice_mem hκ hs hreal (Set.subset_univ _) hU ρ hfin C hC t P r).trans
    (rawContractionDomain_iff D.contraction (Fin.elim0,r)).symm

def rawSelectedSliceRestrictedEquiv : P.domain ≃ rvObjectDomain D.contraction.contractionObject where
  toFun u := ⟨u.val,(rawSelectedSlice_restricted_domain hκ hs hreal hU ρ hfin C hC t D P u.val).mp u.property⟩
  invFun u := ⟨u.val,(rawSelectedSlice_restricted_domain hκ hs hreal hU ρ hfin C hC t D P u.val).mpr u.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

def gammaRawSelectedSliceRestrictedIso :
    GammaRVIso P.toGamma.toGammaRVObject
      (gammaRawFiniteContraction hκ hs (small_union_range hκ B.real hreal (fun j => (t j).val))
        (Set.subset_univ _) (rvLabelSlice_gamma U hU ρ t) (rvLabelSlice_finite U hU ρ hfin t)
        D.contraction D.gamma).toGammaRVObject := by
  let E := rawSelectedSliceRestrictedEquiv hκ hs hreal hU ρ hfin C hC t D P
  apply gammaIsoOfFiniteEquiv P.toGamma
    (gammaRawFiniteContraction hκ hs (small_union_range hκ B.real hreal (fun j => (t j).val))
      (Set.subset_univ _) (rvLabelSlice_gamma U hU ρ t) (rvLabelSlice_finite U hU ρ hfin t)
      D.contraction D.gamma) E (gammaIsoRefl P.toGamma).graph
  intro u
  have hPv := volumeSlicePresentation_volume
    (gammaSwapVolumeBlocks (gammaRawSelectedContraction hκ hs hreal (Set.subset_univ _) hU ρ hfin C hC)) t P u
  have hv : (P.volume u).val = u.val ∘ C.volumeIndex := by
    rw [gammaRawSelectedPrepend_value] at hPv
    exact hPv.trans (funext fun j => Fin.append_right _ _ j)
  have hDv : gammaVolumeValue
      (gammaRawFiniteContraction hκ hs (small_union_range hκ B.real hreal (fun j => (t j).val))
        (Set.subset_univ _) (rvLabelSlice_gamma U hU ρ t) (rvLabelSlice_finite U hU ρ hfin t)
        D.contraction D.gamma).toGammaRVObject (E u) = u.val ∘ C.volumeIndex := by
    change u.val ∘ D.contraction.volumeIndex = _
    rw [D.volumeIndex]
  exact congrArg (fun z : Fin n → RV (M := M) => rawWeight (fun j => (z j).val)) (hv.trans hDv.symm)

end IntegrationInACVF.Section6.FiniteRV
