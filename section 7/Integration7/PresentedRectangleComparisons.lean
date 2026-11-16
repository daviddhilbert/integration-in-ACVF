module

public import Integration7.RectangleOppositeOrderComparisons
public import Integration7.FixedLabelContractionConstantDensities
public import Integration7.FixedLabelSameOrderComparisons
public import Integration7.VolumeContextJoins

@[expose] public section

/-! The rectangle comparison applies to any equal actual native presentation,
retaining the supplied contractions and their selected density objects. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {d : ℕ}

set_option maxHeartbeats 1200000 in
theorem rectangle_presented_contraction_comparison
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hgamma : Cardinal.mk P.gamma < C.κ) (γ : Values.Gamma (M := M)) (hγ : γ ∈ P.gamma) (hγ1 : 1 < γ)
    (hPC : P.real ⊆ (C.base : Set M)) (hNames : commonRealNames P ⊆ (C.base : Set M))
    (hGeneric : ∀ {p : ℕ} (x : Fin p → VF (M := M)), AlgebraicIndependent (vfParameterField P.real) x →
      AlgebraicIndependent (vfParameterField (C.base : Set M)) x)
    (D E : DefSet (M := M) (C.base : Set M) 1 0)
    (hD : GammaSetDefinable P (carrier D)) (hE : GammaSetDefinable P (carrier E))
    (Z : DefSet (M := M) (C.base : Set M) 2 0) (hZ : GammaSetDefinable P (carrier Z))
    (hRect : Z = nativeUnaryProductDomain D E)
    (z : Fin d → RV (M := M)) (hz : ∀ j, (z j).val ∈ (C.base : Set M))
    (hzΓ : DefinableOverBase P (fun _ : Fin d => .rv) {fun j => (z j).val})
    (j : Fin d) (η : RV (M := M)) (hj : z j = η) (hη : η.val ∈ C.base) (hη0 : η ≠ 0)
    (T : IntegrationInACVF.Section5.StandardContraction (fixedRVLabelDomain Z z hz) (Equiv.refl _))
    (W : IntegrationInACVF.Section5.StandardContraction (fixedRVLabelDomain Z z hz) (Equiv.swap 0 1))
    (hT : IntegrationInACVF.Section5.GammaProgramDefinable P T.program)
    (hW : IntegrationInACVF.Section5.GammaProgramDefinable P W.program) :
    let hsmall : Cardinal.mk P.real < C.κ := (Cardinal.mk_le_mk_of_subset hPC).trans_lt C.small
    let U := fixedLabelContractionGammaObject C.uncountable.le C.saturated hsmall hc C hPC Z hZ z hz hzΓ j η hj hη0 T hT
    let V := fixedLabelContractionGammaObject C.uncountable.le C.saturated hsmall hc C hPC Z hZ z hz hzΓ j η hj hη0 W hW
    ∃ (K : BaseContext M) (hCK : (C.base : Set M) ⊆ (K.base : Set M)),
      GammaVolumeBlowupEquivalent P (K.base : Set M) 1 (U.extend hCK) (V.extend hCK) := by
  cases hRect
  exact rectangle_opposite_order_contraction_comparison hc C hgamma γ hγ hγ1 hPC hNames hGeneric
    D E hD hE z hz hzΓ j η hj hη hη0 T W hT hW

end IntegrationInACVF.Section7
