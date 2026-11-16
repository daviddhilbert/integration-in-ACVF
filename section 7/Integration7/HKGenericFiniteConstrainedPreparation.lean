import Integration7.GenericFiniteIsomorphismPreparation
import Integration7.HKConstrainedBijectionCharts

/-! Generic finite-row charts can be prepared while retaining a global
graph constraint. The same finite family is used on every essential cell. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b k : ℕ}

theorem generic_finite_constrained_preparation {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M))
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    (A : DefSet (M := M) (C.base : Set M) p 0) (hA : GammaSetDefinable B (carrier A))
    (F : GammaFiniteRVSchema B p a k) (G : GammaFiniteRVSchema B p b k)
    (K : Set (Fin ((p+a)+b) → M))
    (hrow : ∀ x : Fin p → VFType (M := M), AlgebraicIndependent (vfParameterField B.real) x →
      ∃ H : GammaRelationFormula B p a b (fun _ => .vf), H.val ⊆ K ∧
        (gammaFiniteRowChartSchema F G H).valid (vfValues x)) :
    ∃ J : Finset {H : GammaRelationFormula B p a b (fun _ => .vf) // H.val ⊆ K},
    ∃ D : BaseContext M, ∃ hCD : (C.base : Set M) ⊆ (D.base : Set M),
    ∃ l : ℕ, ∃ Z : DefSet (M := M) (D.base : Set M) p l,
    ∃ T : SpecialBijection (extendBase A hCD) Z,
    ∃ hT : GammaChainDefinable B T.chain, IsRVPullback (carrier Z) ∧
      (∀ q : Z, (GammaParameterRecode.prepared T hT).ObjectAgreement F
        (rawVFParameter (T.inverseMap q).val) (rawPreparedKey q.val)) ∧
      (∀ q : Z, (GammaParameterRecode.prepared T hT).ObjectAgreement G
        (rawVFParameter (T.inverseMap q).val) (rawPreparedKey q.val)) ∧
      ∀ q : Z, (∀ i, (rv (q.val.1 i)).val ≠ iRVZero) →
        ∃ H ∈ J, (gammaFiniteRowChartSchema
          ((GammaParameterRecode.prepared T hT).object F)
          ((GammaParameterRecode.prepared T hT).object G)
          ((GammaParameterRecode.prepared T hT).relation H.val)).valid (rawPreparedKey q.val) := by
  obtain ⟨J,hJ⟩ := gamma_finite_witnesses_at_generic_points B hκ hs hr hg
    (fun H : {H : GammaRelationFormula B p a b (fun _ => .vf) // H.val ⊆ K} =>
      {z | (gammaFiniteRowChartSchema F G H.val).valid z})
    (fun H => (gammaFiniteRowChartSchema F G H.val).valid_definable) (by
      intro x hx
      obtain ⟨H,hHK,hH⟩ := hrow x hx
      exact ⟨⟨H,hHK⟩,hH⟩)
  obtain ⟨D,hCD,l,Z,T,hT,hZ,hFA,hGA,hAg⟩ := prepare_finite_isomorphism_geometry_in_context
    C hBC A hA F G (J.image Subtype.val)
  refine ⟨J,D,hCD,l,Z,T,hT,hZ,hFA,hGA,?_⟩
  intro q hq
  obtain ⟨y,hy,hind⟩ := exists_generic_inverse_in_prepared_cell hc D T hZ q hq
  obtain ⟨H,hHJ,hH⟩ := hJ (T.inverseMap y).val.1
    (independent_over_smaller_real_base (hBC.trans hCD) hind)
  have hRecoded := (GammaParameterRecode.prepared T hT).iso_valid
    (gammaFiniteRowChartSchema F G H.val) (rawVFParameter (T.inverseMap y).val)
    (rawPreparedKey y.val) (fun i => ((flatKey y.val).2 i).property)
    ⟨hFA y,hGA y,hAg H.val (Finset.mem_image.mpr ⟨H,hHJ,rfl⟩) y⟩ hH
  have hk : rawPreparedKey y.val = rawPreparedKey q.val :=
    congrArg (fun t => fun i => (t.2 i).val) ((flatKey_eq_iff _ _).mpr hy)
  exact ⟨H,hHJ,hk ▸ hRecoded⟩

end IntegrationInACVF.Section7.HK
