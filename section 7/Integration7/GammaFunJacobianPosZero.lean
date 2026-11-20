import Integration7.GammaFunJacobianZeroCoef

/-! **Jacobian transforms commute with positive coefficients on degree-zero presentations**
(almost everywhere). -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput carrier)
open SpecialTransformations.DefinableGeometry (Map DefSet)
open SpecialTransformations.Section4 (rawMixedSpace rawRVSpace rawVFSpace)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a p : ℕ}

/-- Label coordinates of the degree-zero family inside a positive-coefficient product. -/
def zeroPosBaseIndex (a b p : ℕ) : Fin a → Fin ((a+b)+(p+1)) := fun i => Fin.castAdd (p+1) (Fin.castAdd b i)
/-- Label coordinates of the coefficient inside a positive-coefficient product. -/
def zeroPosCoefIndex (a b p : ℕ) : Fin b → Fin ((a+b)+(p+1)) := fun i => Fin.castAdd (p+1) (Fin.natAdd a i)

theorem mem_zero_family_positive_product (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p)
    (F : HK.ZeroVFVolumeFamily C n a) (q : Point (M := M) n ((a+U.underlying.obj.arity)+(p+1))) :
    q ∈ (HK.selectedZeroFamilyPositiveProduct U F).domain.carrier ↔
      (q.1,q.2 ∘ zeroPosBaseIndex a U.underlying.obj.arity p) ∈ F.domain.carrier ∧
      ∃ h : q.2 ∘ zeroPosCoefIndex a U.underlying.obj.arity p ∈ U.underlying.obj.domain.carrier,
        U.underlying.obj.value ⟨_,h⟩ = q.2 ∘ Fin.natAdd (a+U.underlying.obj.arity) := by
  constructor
  · rintro ⟨w,hw⟩
    have hv := ordinary_family_positive_coefficient_projection_value F.toOrdinary U w
    have hm := (mem_mixed_rv_factor_domain F.domain U.underlying.obj.domain w.val.1 w.val.2).mp w.property
    have hq : (appendMixedRVMap (F.mulConstant U).volume w).val = q := hw
    rw [append_mixed_rv_map_value] at hq
    subst hq
    refine ⟨?_,?_⟩
    · change (w.val.1,Fin.append w.val.2 _ ∘ zeroPosBaseIndex a U.underlying.obj.arity p) ∈ F.domain.carrier
      have : Fin.append w.val.2 ((F.mulConstant U).volume w).val ∘ zeroPosBaseIndex a U.underlying.obj.arity p =
          w.val.2 ∘ Fin.castAdd U.underlying.obj.arity := funext fun i => by simp [zeroPosBaseIndex]
      rw [this]
      exact hm.1
    · have h2 : Fin.append w.val.2 ((F.mulConstant U).volume w).val ∘ zeroPosCoefIndex a U.underlying.obj.arity p = w.val.2 ∘ Fin.natAdd a :=
        funext fun i => by simp [zeroPosCoefIndex]
      refine ⟨by
        change Fin.append w.val.2 ((F.mulConstant U).volume w).val ∘ zeroPosCoefIndex a U.underlying.obj.arity p ∈ _
        rw [h2]
        exact hm.2,?_⟩
      change _ = Fin.append w.val.2 ((F.mulConstant U).volume w).val ∘ Fin.natAdd (a+U.underlying.obj.arity)
      have h3 : Fin.append w.val.2 ((F.mulConstant U).volume w).val ∘ Fin.natAdd (a+U.underlying.obj.arity) =
          ((F.mulConstant U).volume w).val := funext fun i => by simp
      rw [h3]
      change _ = U.underlying.obj.value (ordinaryFamilyPositiveCoefficientProjection F.toOrdinary U w)
      congr 1
      apply Subtype.ext
      exact (show _ = w.val.2 ∘ Fin.natAdd a from h2).trans hv.symm
  · rintro ⟨h1,h2,hv⟩
    let w0 : (Fin n → VFType (M := M)) × (Fin (a+U.underlying.obj.arity) → CanonicalRV.RVSort M) := (q.1,q.2 ∘ Fin.castAdd (p+1))
    have hw0 : w0 ∈ (mixedRVFactorDomain F.domain U.underlying.obj.domain).carrier :=
      (mem_mixed_rv_factor_domain F.domain U.underlying.obj.domain w0.1 w0.2).mpr ⟨h1,h2⟩
    refine ⟨⟨w0,hw0⟩,?_⟩
    show (appendMixedRVMap (F.mulConstant U).volume ⟨w0,hw0⟩).val = q
    rw [append_mixed_rv_map_value]
    refine Prod.ext rfl ?_
    have hvol : ((F.mulConstant U).volume ⟨w0,hw0⟩).val = q.2 ∘ Fin.natAdd (a+U.underlying.obj.arity) := by
      refine Eq.trans ?_ hv
      change U.underlying.obj.value (ordinaryFamilyPositiveCoefficientProjection F.toOrdinary U ⟨w0,hw0⟩) = _
      congr 1
      apply Subtype.ext
      exact ordinary_family_positive_coefficient_projection_value F.toOrdinary U ⟨w0,hw0⟩
    rw [hvol]
    exact Fin.append_castAdd_natAdd

end IntegrationInACVF.Section7
