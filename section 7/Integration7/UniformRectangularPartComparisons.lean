module

public import Integration7.NativeCellFamilyPartitionDomains
public import Integration7.RectangleFamilyAllOrderComparisons

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The actual rectangular piece of the constructed cell-family
partition now has its comparison in every specified VF-two order. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7.UniformMixedCellPresentation
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {m : ℕ}

theorem rectangular_native_part_contractions_compare
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hgamma : Cardinal.mk G.gamma < C.κ)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ G.gamma) (hγ1 : 1 < γ)
    (hGC : G.real ⊆ (C.base : Set M)) (hNames : commonRealNames G ⊆ (C.base : Set M))
    (hGeneric : ∀ {p : ℕ} (x : Fin p → VF (M := M)), AlgebraicIndependent (vfParameterField G.real) x →
      AlgebraicIndependent (vfParameterField (C.base : Set M)) x)
    {A : DefSet (M := M) (C.base : Set M) 2 m} (F : UniformMixedCellPresentation G (carrier A))
    (hfin : ∀ x : Fin 2 → VF (M := M), {r : Fin m → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (δ : Fin (m+F.arity)) (hδ : ∀ p : F.rectangularNativePart hNames, (p.val.2 δ).val ≠ iRVZero)
    {σ τ : Equiv.Perm (Fin 2)} (T : StandardContraction (F.rectangularNativePart hNames) σ)
    (W : StandardContraction (F.rectangularNativePart hNames) τ)
    (hT : GammaProgramDefinable G T.program) (hW : GammaProgramDefinable G W.program) :
    let hreal : Cardinal.mk G.real < C.κ := (Cardinal.mk_le_mk_of_subset hGC).trans_lt C.small
    let Z := F.rectangularNativePart hNames
    let hZ := F.rectangular_native_part_gamma hNames
    let hfinZ := F.rectangular_native_part_finite_labels hNames hfin
    ∃ D : BaseContext M, ∃ hCD : (C.base : Set M) ⊆ (D.base : Set M),
      GammaVolumeBlowupEquivalent G (D.base : Set M) 1
        ((retainedDensityContractionGammaObject C.uncountable.le C.saturated hreal hc C hGC Z hZ hfinZ δ hδ T hT).extend hCD)
        ((retainedDensityContractionGammaObject C.uncountable.le C.saturated hreal hc C hGC Z hZ hfinZ δ hδ W hW).extend hCD) :=
  rectangle_family_contractions_compare hc C hgamma γ hγ hγ1 hGC hNames hGeneric _
    (F.rectangular_native_part_gamma hNames) (F.rectangular_native_part_finite_labels hNames hfin)
    (F.rectangular_native_part_fibres hNames) δ hδ T W hT hW

end IntegrationInACVF.Section7.UniformMixedCellPresentation
