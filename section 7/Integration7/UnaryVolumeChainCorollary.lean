import Integration7.UnarySpecialVolumeChains

/-! The unary volume version of Corollary 6.10: an actual special
bijection produces forward volume blowups and the exact final comparison. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section5 (SpecialBijection pullbackObject rvObjectArity rvObjectVolume)
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem corollary_6_10_unary_volume
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F : @RVFiniteObject M N (C.base : Set M) 1)
    (ω : VolumeForm (canonicalFiniteRVObject hc F).obj.domain)
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 (rvObjectArity F.obj)}
    (h : @Section6.PresentsLift M N hN (C.base : Set M) 1 F.obj (Section6.normalizedPointSet A))
    (δ : Fin (rvObjectArity F.obj)) (hDensity : ∀ u, ω.value u = u.val δ)
    {l : ℕ} {Z : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 l}
    (T : SpecialBijection A Z) :
    ∃ hZF : @Map.FiniteFibres LRV M N _ _ (C.base : Set M) _ _ (rvObjectVolume (pullbackObject Z)),
    ∃ hδZ : ∀ z : Z, (z.val.2 (T.chain.labelIndex δ)).val ≠ iRVZero,
    ∃ W : PositiveRVVolumeObject (M := M) (C.base : Set M) 0,
      IteratedVolumeBlowup T.length
        (⟨canonicalFiniteRVObject hc F,ω⟩ : PositiveRVVolumeObject (M := M) (C.base : Set M) 0) W ∧
      Nonempty (RVVolumeIso W (pullbackCoordinateVolumeObject hc Z hZF (T.chain.labelIndex δ) hδZ)) := by
  obtain ⟨hZF,hδZ,W,hW,he⟩ := (unary_special_volume_chain_pair hc C T.chain).1
    (@RVObject.domain M N (C.base : Set M) 1 F.obj) (@RVObject.volume M N (C.base : Set M) 1 F.obj)
    F.property ω h δ hDensity T.alternating
  change IteratedVolumeBlowup T.length
    (⟨canonicalFiniteRVObject hc F,ω⟩ : PositiveRVVolumeObject (M := M) (C.base : Set M) 0) W at hW
  exact ⟨hZF,hδZ,W,hW,he⟩

end IntegrationInACVF.Section7
