module

public import Integration7.FixedLabelTranslationCommonBlowups

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Corollary7.6 with the actual identity map compares any two specified
same-order contractions of a fixed-label domain, preserving its literal
selected density and the original Gamma base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open SpecialTransformations.Section9
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {n d : ℕ}

theorem fixed_label_same_order_contraction_common_blowup {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk P.real < κ) (hgamma : Cardinal.mk P.gamma < κ)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ P.gamma) (hγ1 : 1 < γ)
    (hPC : P.real ⊆ (C.base : Set M))
    (hGeneric : ∀ {p : ℕ} (x : Fin p → VF (M := M)), AlgebraicIndependent (vfParameterField P.real) x →
      AlgebraicIndependent (vfParameterField (C.base : Set M)) x)
    (A : DefSet (M := M) (C.base : Set M) (n+1) 0) (hA : GammaSetDefinable P (carrier A))
    (z : Fin d → RV (M := M)) (hz : ∀ j, (z j).val ∈ (C.base : Set M))
    (hzΓ : DefinableOverBase P (fun _ : Fin d => .rv) {fun j => (z j).val})
    (j : Fin d) (η : RV (M := M)) (hj : z j = η) (hη0 : η ≠ 0)
    {σ : Equiv.Perm (Fin (n+1))} (T E : StandardContraction (fixedRVLabelDomain A z hz) σ)
    (hT : GammaProgramDefinable P T.program) (hE : GammaProgramDefinable P E.program) :
    let U := fixedLabelContractionGammaObject hκ hs hreal hc C hPC A hA z hz hzΓ j η hj hη0 T hT
    let V := fixedLabelContractionGammaObject hκ hs hreal hc C hPC A hA z hz hzΓ j η hj hη0 E hE
    ∃ (D : BaseContext M) (hCD : (C.base : Set M) ⊆ (D.base : Set M)),
      GammaVolumeBlowupEquivalent P (D.base : Set M) n (U.extend hCD) (V.extend hCD) := by
  intro U V
  let H := fixedRVLabelDomain A z hz
  let ω := fixedRVLabelDensityForm hc A z hz j η hj hη0
  have hH := gamma_fixed_rv_label_domain A hA z hz hzΓ
  have hfin := fixed_pure_rv_label_fibres_finite A z hz
  have hJ := vfJacobianOne_of_preservesVF hc C (Nat.zero_lt_succ n) (rawSpecialMap hc (Map.id H)) (fun _ => rfl)
  have hm : PreservesVFVolume ω ω (rawSpecialMap hc (Map.id H)) := hJ.mono (fun p h =>
    ⟨1,h,by rw [RVOperations.rv_one,mul_one];rfl⟩)
  have hGeom := standard_relative_volume_schema_comparison_of_generic_extension hc C hκ hs hreal hgamma γ hγ hγ1
    hPC hGeneric H H hH hH hfin hfin (Map.id H) Function.bijective_id (gamma_identity_graph H hH)
    ω ω (Fin.natAdd 0 j) (Fin.natAdd 0 j) (fun _ => rfl) (fun _ => rfl) hm (unaryRelative_id (σ 0)) T E hT hE
  exact finite_standard_volume_comparison_of_geometric_rows hc C hκ hs hreal hPC H H hH hH hfin hfin T E hT hE
    (Fin.natAdd 0 j) (Fin.natAdd 0 j)
    (fun p => raw_fixed_rv_label_density_nonzero hc A z hz j η hj hη0 ⟨p.val,p.property⟩)
    (fun p => raw_fixed_rv_label_density_nonzero hc A z hz j η hj hη0 ⟨p.val,p.property⟩) hGeom

end IntegrationInACVF.Section7
