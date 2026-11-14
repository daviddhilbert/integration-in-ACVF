import Integration7.FiniteRVMapBounds

/-! The exceptional map in a volume-isomorphism certificate has a uniform
finite fibre bound. The bound is derived, rather than added to the hypotheses. -/

noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

theorem RVVolumeIsoCertificate.exists_uniform_bound
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k} {e : U.essential ≅ V.essential}
    (H : RVVolumeIsoCertificate U V e) :
    ∃ N : ℕ, ∀ y : Fin H.arity → M, (∀ i, iRV (y i)) →
      {x : Fin U.essential.obj.arity → M |
        (y,x) ∈ rawRVMapReverseGraph H.projection}.ncard ≤ N :=
  finiteRVMap_uniform_bound hc C.uncountable.le C.saturated C.small H.projection H.projection_finite

theorem RVVolumeIso.exists_bounded_certificate
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k} (e : RVVolumeIso U V) :
    ∃ H : RVVolumeIsoCertificate U V e.iso, ∃ N : ℕ,
      ∀ y : Fin H.arity → M, (∀ i, iRV (y i)) →
        {x : Fin U.essential.obj.arity → M |
          (y,x) ∈ rawRVMapReverseGraph H.projection}.ncard ≤ N := by
  obtain ⟨H⟩ := e.exists_finite_certificate hc C
  obtain ⟨N,hN⟩ := H.exists_uniform_bound hc C
  exact ⟨H,N,hN⟩

end IntegrationInACVF.Section7
