module

public import Integration7.StandardRestrictionNormalizedCarriers
public import Integration7.RetainedDensityContractionObjects
public import Integration7.GammaVolumeRestrictionIdentities

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! An actual restricted contraction's normalized volume object is
the literal restriction of the original normalized volume object to
its label domain. The identity map preserves all coordinates and density. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaSetDefinable rvObjectDomain carrier)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {k a d : ℕ}

set_option maxHeartbeats 2400000 in
theorem standard_restriction_volume_identification {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hreal : Cardinal.mk G.real < κ)
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hGC : G.real ⊆ (C.base : Set M))
    (U A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (k+1) a)
    (hU : GammaSetDefinable G (carrier U)) (hA : GammaSetDefinable G (carrier A))
    (hfinU : ∀ x : Fin (k+1) → SpecialTransformations.Section5.VF (M := M),
      {r : Fin a → SpecialTransformations.Section5.RV (M := M) | (x,r) ∈ carrier U}.Finite)
    (hfinA : ∀ x : Fin (k+1) → SpecialTransformations.Section5.VF (M := M),
      {r : Fin a → SpecialTransformations.Section5.RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (ρ : Fin d → Fin a) (R : Set (Point (M := M) 0 d)) (hR : GammaSetDefinable G R)
    (hNames : commonRealNames G ⊆ (C.base : Set M))
    {σ : Equiv.Perm (Fin (k+1))} (T : StandardContraction U σ) (hT : GammaProgramDefinable G T.program)
    (D : StandardTargetRestrictionPresentation (G := G) T A
      (rvLabelCut T.target (gamma_program_final_set T.program hT)
        (fun j => suffixIndex T.program.rvArity_le (ρ j)) R hR hNames))
    (δ : Fin a) (hδU : ∀ p : U, (p.val.2 δ).val ≠ iRVZero)
    (hδA : ∀ p : A, (p.val.2 δ).val ≠ iRVZero) :
    let X := retainedDensityContractionGammaObject hκ hs hreal hc C hGC U hU hfinU δ hδU T hT
    let Y := retainedDensityContractionGammaObject hκ hs hreal hc C hGC A hA hfinA δ hδA D.contraction D.gamma
    let hSub : Y.val.underlying.obj.domain.carrier ⊆ X.val.underlying.obj.domain.carrier :=
      fun r hr => ((D.normalized_carrier hT ρ R hR hNames r).mp hr).1
    ∃ e : RVVolumeIso Y.val (X.val.restrict Y.val.underlying.obj.domain hSub), e.GammaDefinable G := by
  intro X Y hSub
  let Z := X.val.restrict Y.val.underlying.obj.domain hSub
  let f : Map Y.val.underlying.obj.domain Z.underlying.obj.domain := Map.id _
  let i : Y.val.underlying ≅ Z.underlying := rvFiniteIsoOfAmbient
    (rvIsoOfVolumePreservingBijection f Function.bijective_id (fun _ => rfl))
  let e := RVVolumeIso.of_preserving_coordinates_full hc C i (fun _ => rfl) (fun _ => rfl)
  exact ⟨e,gamma_volume_iso_of_label_identity hc e Y.property rfl (fun _ => rfl)⟩

end IntegrationInACVF.Section7
