module

public import Integration7.GradedAEVolumePrefixFubini
public import Integration7.AppendedVolumePrefixFubini

@[expose] public section

/-! Every homogeneous component of iterated graded integration is the
actual iterated head integral. Positive inputs retain the existing prefix
map, and ordinary inputs enter positive degree after their first head. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open scoped DirectSum

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

def aeVolumeFunctionComponentPrefixIntegral : (r n j : ℕ) →
    ZeroHom (AEVolumeFunctionComponent hc C (n+r) j) (AEVolumeFunctionComponent hc C n (appendVolumeDegree r j))
  | 0,n,j => ZeroHom.id _
  | r+1,n,j => (aeVolumeFunctionComponentPrefixIntegral r n (j+1)).comp {
      toFun := aeVolumeFunctionComponentHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (n+r) j
      map_zero' := ae_volume_component_head_integral_zero hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (n+r) j }

theorem graded_ae_volume_prefix_integral_of : ∀ (r n j : ℕ) (f : AEVolumeFunctionComponent hc C (n+r) j),
    gradedAEVolumePrefixIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n
        (DirectSum.of (AEVolumeFunctionComponent hc C (n+r)) j f) =
      DirectSum.of (AEVolumeFunctionComponent hc C n) (appendVolumeDegree r j)
        (aeVolumeFunctionComponentPrefixIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n j f) := by
  intro r
  induction r with
  | zero => intro n j f; rfl
  | succ r ih =>
    intro n j f
    rw [graded_ae_volume_prefix_integral_succ]
    exact (congrArg (gradedAEVolumePrefixIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n)
      (graded_ae_volume_head_integral_of hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (n+r) j f)).trans
      (ih n (j+1) (aeVolumeFunctionComponentHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (n+r) j f))

theorem ae_volume_component_prefix_integral_positive_heq : ∀ (r n k : ℕ) (f : AERVVolumeFunction hc C (n+r) k),
    HEq (aeVolumeFunctionComponentPrefixIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n (k+1) f)
      (aeRVVolumeFunctionPrefixIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n k f) := by
  intro r
  induction r with
  | zero => intro n k f; rfl
  | succ r ih =>
    intro n k f
    exact ih n (k+1) (aeRVVolumeFunctionHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f)

theorem ae_volume_component_prefix_integral_ordinary_heq (r n : ℕ)
    (f : AEOrdinaryRVVolumeFunction hc C (n+(r+1))) :
    HEq (aeVolumeFunctionComponentPrefixIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (r+1) n 0 f)
      (aeRVVolumeFunctionPrefixIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n 0
        (aeOrdinaryRVVolumeFunctionHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f)) :=
  ae_volume_component_prefix_integral_positive_heq hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n 0 _

end IntegrationInACVF.Section7
