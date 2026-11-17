module

public import Integration7.FixedLabelTranslationContractionComparisons
public import Integration7.GammaNamesGenericParameters
public import Integration7.GammaRelativeTranslations
public import Integration7.OriginalBaseRelativeVolumeComparisons

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Corollary7.6 compares arbitrary specified contractions before and
following an actual translation, with every old label and the literal
retained density fixed. This is over the original Gamma base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {n d : ℕ}

set_option maxHeartbeats 1200000 in
theorem gamma_named_fixed_label_translation_contraction_geometry
    (hc : CanonicalStructure.IsCanonical (M := M)) (C0 : BaseContext M)
    (hP0 : P.real ⊆ (C0.base : Set M)) (hBase : P.real = (C0.base : Set M))
    (hgamma : Cardinal.mk P.gamma < C0.κ)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ P.gamma) (hγ1 : 1 < γ) :
    let C := gammaNamesContainingVolumeContext C0 P hP0 hgamma
    ∀ (A : DefSet (M := M) (C.base : Set M) (n+1) 0) (hA : GammaSetDefinable P (carrier A))
    (i : Fin (n+1))
    (c : Map A (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) (C.base : Set M)))
    (hC : ∀ p q : A, erase i p.val = erase i q.val → (c p).val 0 = (c q).val 0)
    (hcΓ : GammaScalarGraphDefinable P (fun p a => ∃ q : A, q.val = p ∧ (c q).val 0 = a))
    (z : Fin d → RV (M := M)) (hz : ∀ j, (z j).val ∈ (C.base : Set M))
    (hzΓ : DefinableOverBase P (fun _ : Fin d => .rv) {fun j => (z j).val})
    (j : Fin d) (η : RV (M := M)) (hj : z j = η) (hη0 : η ≠ 0)
    {σ : Equiv.Perm (Fin (n+1))} (hσ : σ 0 = i)
    (T : StandardContraction (fixedRVLabelDomain A z hz) σ)
    (E : StandardContraction (fixedRVLabelDomain (relativeTranslationImage A i c) z hz) σ)
    (hT : GammaProgramDefinable P T.program) (hE : GammaProgramDefinable P E.program),
    (gammaSelectedVolumeSchema T.target (gamma_program_final_set T.program hT) T.volumeIndex
      (suffixIndex T.program.rvArity_le (Fin.natAdd 0 j))).commonByGammaGeometry
    (gammaSelectedVolumeSchema E.target (gamma_program_final_set E.program hE) E.volumeIndex
      (suffixIndex E.program.rvArity_le (Fin.natAdd 0 j)))
      (fun j : Fin 0 => (Fin.elim0 j : VF (M := M)).val) := by
  intro C A hA i c hC hcΓ z hz hzΓ j η hj hη0 σ hσ T E hT hE
  have hPC : P.real ⊆ (C.base : Set M) := fun _ hx =>
    gamma_names_containing_volume_context_contains C0 P hP0 hgamma (Or.inl (hP0 hx))
  exact fixed_label_translation_contraction_geometry hc C C0.uncountable.le C0.saturated
    ((Cardinal.mk_le_mk_of_subset hP0).trans_lt C0.small) hgamma γ hγ hγ1 hPC
    (fun x hx => gamma_names_context_preserves_independence hc C0 P hP0 hgamma hBase x hx)
    A hA i c hC hcΓ z hz hzΓ j η hj hη0 hσ T E hT hE

end IntegrationInACVF.Section7
