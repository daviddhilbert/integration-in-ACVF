import IntegrationSection6.GammaFocusAdmissibility
import IntegrationSection6.GammaLiftVolumeRecovery
import IntegrationSection6.PartialFocusLocus
import IntegrationSection6.NormalizedLifts

/-! Active focus loci retain their full original-Gamma RV-object graphs.
Their underlying literal lift is identified without enlarging the base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem normalizedPresentsLift_carrier {U : @RVObject M N S n}
    {A : SpecialTransformations.Section5.DefSet (M := M) S n (rvObjectArity U)}
    (h : @PresentsLift M N hN S n U (normalizedPointSet A)) :
    carrier A = carrier (rawLift U) := by
  ext p
  exact h p

theorem normalizedPresentsLift_nonzero {U : @RVObject M N S n}
    {A : SpecialTransformations.Section5.DefSet (M := M) S n (rvObjectArity U)}
    (h : @PresentsLift M N hN S n U (normalizedPointSet A)) {i : Fin n}
    (hn : ∀ p ∈ carrier A, p.1 i ≠ (0 : VF (M := M))) :
    letI : LRV.Structure M := N
    letI : M ⊨ Axioms.ACVF := hN
    ∀ u : U.domain, U.value u i ≠ 0 := by
  intro u
  obtain ⟨p,_,hp⟩ := @PresentsLift.representative M N hN S n U (normalizedPointSet A) h u
  have hnp : p.val.1 i ≠ @Zero.zero (@VF M N) (@vfInstZero M N hN) := by
    rw [vfZero_normalize]
    exact hn p.val p.property
  letI := N
  letI := hN
  intro hz
  exact (RVOperations.rv_ne_zero _).mpr hnp ((congrFun hp i).trans hz)

theorem gamma_fullFocus_volume_algebraic {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk B.real < κ)
    {U : @RVObject M N S n}
    {A : SpecialTransformations.Section5.DefSet (M := M) S n (rvObjectArity U)}
    (h : @PresentsLift M N hN S n U (normalizedPointSet A))
    {i : Fin n} {k : Fin (rvObjectArity U)} (D : Focus A i k)
    (hA : GammaSetDefinable B (carrier A)) (hD : GammaFocusDefinable B D)
    (hfull : carrier A ⊆ D.locus) (u : rvObjectDomain U) :
    AlgebraicAt (@coordinateBase M N n B.real i (@RVObject.value M N S n U u)) .rv
      ((@RVObject.value M N S n U u) i).val := by
  have hAP := (pullback_normalize (carrier A)).mp
    (@PresentsLift.pullback M N hN S n U (normalizedPointSet A) h)
  obtain ⟨p,_,hp⟩ := @PresentsLift.representative M N hN S n U (normalizedPointSet A) h u
  let a : A := ⟨p.val,p.property⟩
  have ha := gamma_fullFocus_label_algebraic hκ hs hsmall D hAP hA hD hfull a
  have he : (fun j => @rv M sM hM (p.val.1 j)) = @RVObject.value M N S n U u := by
    funext j
    exact (rv_normalize _).symm.trans (congrFun hp j)
  change AlgebraicAt (coordinateBase B.real i (fun j => @rv M sM hM (p.val.1 j))) .rv
    ((fun j => @rv M sM hM (p.val.1 j)) i).val at ha
  rwa [he] at ha

end IntegrationInACVF.Section6
