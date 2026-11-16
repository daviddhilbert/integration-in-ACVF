module

public import Integration7.NormalizedVolumeHeadFubini
public import Integration7.GradedAEVolumePrefixFubini
public import Integration7.AppendedVolumePrefixFubini

@[expose] public section

/-! Iterating the actual normalized linear head operator gives a
normalized linear partial integral for every VF prefix, with its
geometric positive-generator formula and full total Fubini identity. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

def normalizedVolumePrefixIntegral : (r n : ℕ) →
    NormalizedVolumeFunction hc C (n+r) →ₗ[NormalizedRVVolumeRing hc C] NormalizedVolumeFunction hc C n
  | 0,n => LinearMap.id
  | r+1,n => (normalizedVolumePrefixIntegral r n).comp
      (normalizedVolumeHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (n+r))

theorem normalized_volume_prefix_integral_positive : ∀ (r n k : ℕ) (f : AERVVolumeFunction hc C (n+r) k),
    normalizedVolumePrefixIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n
      (normalizedPositiveVolumeFunction hc C (n+r) k f) =
    normalizedVolumeFunctionGenerator hc C n
      (gradedAEVolumePrefixIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n
        (DirectSum.of (AEVolumeFunctionComponent hc C (n+r)) (k+1) f)) := by
  intro r
  induction r with
  | zero => intro n k f; rfl
  | succ r ih =>
    intro n k f
    have hHead := congrArg (normalizedVolumePrefixIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n)
      (normalized_volume_head_integral_positive hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (n+r) k f)
    have hPrefix := ih n (k+1) (aeRVVolumeFunctionHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f)
    have hRaw := congrArg (fun g => normalizedVolumeFunctionGenerator hc C n
      (gradedAEVolumePrefixIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n g))
      (graded_ae_volume_head_integral_of hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (n+r) (k+1) f).symm
    exact hHead.trans (hPrefix.trans hRaw)

theorem normalized_volume_prefix_integral_positive_value : ∀ (r n k : ℕ) (f : AERVVolumeFunction hc C (n+r) k),
    normalizedVolumePrefixIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n
      (normalizedPositiveVolumeFunction hc C (n+r) k f) =
    normalizedPositiveVolumeFunction hc C n (appendVolumeDegree r k)
      (aeRVVolumeFunctionPrefixIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n k f) := by
  intro r
  induction r with
  | zero => intro n k f; rfl
  | succ r ih =>
    intro n k f
    have hHead := congrArg (normalizedVolumePrefixIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n)
      (normalized_volume_head_integral_positive hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (n+r) k f)
    exact hHead.trans (ih n (k+1) (aeRVVolumeFunctionHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f))

theorem normalized_volume_prefix_total_fubini : ∀ r n : ℕ,
    (normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n).comp
      (normalizedVolumePrefixIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n) =
    normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (n+r) := by
  intro r
  induction r with
  | zero => intro n; rfl
  | succ r ih =>
    intro n
    change ((normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n).comp
      (normalizedVolumePrefixIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n)).comp
        (normalizedVolumeHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (n+r)) = _
    rw [ih]
    exact normalized_volume_head_total_fubini hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (n+r)

theorem normalized_volume_prefix_total_value (r n : ℕ) (f : NormalizedVolumeFunction hc C (n+r)) :
    normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
      (normalizedVolumePrefixIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n f) =
    normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (n+r) f :=
  LinearMap.congr_fun (normalized_volume_prefix_total_fubini hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n) f
end IntegrationInACVF.Section7
