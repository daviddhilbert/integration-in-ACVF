module

public import Integration7.PreparedFiniteIsomorphismGeometry
public import Integration7.GenericGammaWitnessCovers
public import Integration7.PreparedGenericRVCells
public import IntegrationSection6.GammaRecodingValidity

@[expose] public section

/-! Isomorphisms of finite rows over generic VF tuples suffice on every
essential prepared RV cell. One finite witness cover is prepared on the
original Gamma base; nonzero cells contain a genuine generic inverse. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b k : ℕ}

theorem generic_finite_isomorphism_preparation_in_context {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M))
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (C₀ : BaseContext M) (hBC₀ : B.real ⊆ (C₀.base : Set M))
    (A : DefSet (M := M) (C₀.base : Set M) p 0) (hA : GammaSetDefinable B (carrier A))
    (F : GammaFiniteRVSchema B p a k) (G : GammaFiniteRVSchema B p b k)
    (hWitness : ∀ x : Fin p → VFType (M := M),
      AlgebraicIndependent (vfParameterField B.real) x →
      ∃ H : GammaRelationFormula B p a b (fun _ => .vf),
        (gammaFiniteRowChartSchema F G H).valid (vfValues x)) :
    ∃ J : Finset (GammaRelationFormula B p a b (fun _ => .vf)),
    ∃ D : BaseContext M, ∃ hC₀D : (C₀.base : Set M) ⊆ (D.base : Set M),
    ∃ l : ℕ, ∃ Z : DefSet (M := M) (D.base : Set M) p l,
    ∃ T : SpecialBijection (extendBase A hC₀D) Z,
    ∃ hT : GammaChainDefinable B T.chain, IsRVPullback (carrier Z) ∧
      (∀ x : Z, (GammaParameterRecode.prepared T hT).ObjectAgreement F
        (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val)) ∧
      (∀ x : Z, (GammaParameterRecode.prepared T hT).ObjectAgreement G
        (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val)) ∧
      ∀ x : Z, (∀ j, (rv (x.val.1 j)).val ≠ iRVZero) →
        ∃ H ∈ J, (gammaFiniteRowChartSchema
          ((GammaParameterRecode.prepared T hT).object F)
          ((GammaParameterRecode.prepared T hT).object G)
          ((GammaParameterRecode.prepared T hT).relation H)).valid (rawPreparedKey x.val) := by
  obtain ⟨J,hJ⟩ := gamma_finite_witnesses_at_generic_points B hκ hs hreal hgamma
    (fun H : GammaRelationFormula B p a b (fun _ => .vf) => {z | (gammaFiniteRowChartSchema F G H).valid z})
    (fun H => (gammaFiniteRowChartSchema F G H).valid_definable) hWitness
  obtain ⟨D,hC₀D,l,Z,T,hT,hZ,hFA,hGA,hAg⟩ := prepare_finite_isomorphism_geometry_in_context
    C₀ hBC₀ A hA F G J
  refine ⟨J,D,hC₀D,l,Z,T,hT,hZ,hFA,hGA,?_⟩
  intro x hx
  obtain ⟨y,hy,hind⟩ := exists_generic_inverse_in_prepared_cell hc D T hZ x hx
  have hindB := independent_over_smaller_real_base (hBC₀.trans hC₀D) hind
  obtain ⟨H,hH,hvalid⟩ := hJ (T.inverseMap y).val.1 hindB
  have hRecoded := (GammaParameterRecode.prepared T hT).iso_valid (gammaFiniteRowChartSchema F G H)
    (rawVFParameter (T.inverseMap y).val) (rawPreparedKey y.val)
    (fun j => ((flatKey y.val).2 j).property) ⟨hFA y,hGA y,hAg H hH y⟩ hvalid
  have hk : rawPreparedKey y.val = rawPreparedKey x.val :=
    congrArg (fun q => fun j => (q.2 j).val) ((flatKey_eq_iff _ _).mpr hy)
  exact ⟨H,hH,hk ▸ hRecoded⟩

end IntegrationInACVF.Section7
