module

public import Integration7.AppendedVolumeHeadFubini

@[expose] public section

/-! Iterated integration of an arbitrary VF prefix, leaving a nonempty
VF base, on the actual almost-everywhere function quotient. The resulting
total integral agrees with total integration of the original function.
Heterogeneous equality records only the arithmetic degree identification. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def aeRVVolumeFunctionPrefixIntegral
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ) :
    (r n k : ℕ) → AERVVolumeFunction hc C (n+r) k → AERVVolumeFunction hc C n (appendVolumeDegree r k)
  | 0,_,_,f => f
  | r+1,n,k,f => aeRVVolumeFunctionPrefixIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n (k+1)
      (aeRVVolumeFunctionHeadIntegral (n := n+r) (k := k) hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f)

theorem ae_rv_volume_function_prefix_integral_zero
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (n k : ℕ) (f : AERVVolumeFunction hc C n k) :
    aeRVVolumeFunctionPrefixIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 0 n k f = f := rfl

theorem ae_rv_volume_function_prefix_integral_succ
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (r n k : ℕ) (f : AERVVolumeFunction hc C (n+(r+1)) k) :
    aeRVVolumeFunctionPrefixIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (r+1) n k f =
      aeRVVolumeFunctionPrefixIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n (k+1)
        (aeRVVolumeFunctionHeadIntegral (n := n+r) hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f) := rfl

theorem ae_rv_volume_function_appended_prefix_fubini
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ) :
    ∀ (r n k : ℕ) (f : AERVVolumeFunction hc C (n+r) k),
      HEq (aeRVVolumeFunctionAppendedIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1
        (aeRVVolumeFunctionPrefixIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n k f))
        (aeRVVolumeFunctionAppendedIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f) := by
  intro r
  induction r with
  | zero => intro n k f; rfl
  | succ r ih =>
    intro n k f
    exact (ih n (k+1)
      (aeRVVolumeFunctionHeadIntegral (n := n+r) hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f)).trans
        (heq_of_eq (ae_rv_volume_function_appended_head_fubini (n := n+r) hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f))

end IntegrationInACVF.Section7
