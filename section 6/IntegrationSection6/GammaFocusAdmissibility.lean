import IntegrationSection6.GammaFocusLabelAlgebraicity
import IntegrationSection6.NormalizedLifts
import IntegrationSection6.NormalizedFocus
import IntegrationSection6.AdmissibleFocusRelabeling

/-! A full genuine Gamma focus forces admissibility in the actual RV
object. Only the original real base is small; the code base can be arbitrary. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem gamma_admissible_of_fullFocus {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk B.real < κ) (hBS : B.real ⊆ S)
    {U : @RVObject M N S n}
    {A : SpecialTransformations.Section5.DefSet (M := M) S n (rvObjectArity U)}
    (h : @PresentsLift M N hN S n U (normalizedPointSet A))
    {i : Fin n} {k : Fin (rvObjectArity U)} (D : Focus A i k)
    (hA : GammaSetDefinable B (carrier A)) (hD : GammaFocusDefinable B D)
    (hfull : carrier A ⊆ D.locus)
    (hnz : letI : LRV.Structure M := N; letI : M ⊨ Axioms.ACVF := hN;
      ∀ u : U.domain, U.value u i ≠ 0) : @Admissible M N S n U i := by
  have hAP := (pullback_normalize (carrier A)).mp
    (@PresentsLift.pullback M N hN S n U (normalizedPointSet A) h)
  have halg (u : rvObjectDomain U) :
      @AlgebraicAt M N (@coordinateBase M N n S i (@RVObject.value M N S n U u)) .rv
        ((@RVObject.value M N S n U u) i).val := by
    obtain ⟨p,_,hp⟩ := @PresentsLift.representative M N hN S n U (normalizedPointSet A) h u
    let a : A := ⟨p.val,p.property⟩
    have ha := gamma_fullFocus_label_algebraic hκ hs hsmall D hAP hA hD hfull a
    have he : (fun j => @rv M sM hM (p.val.1 j)) = @RVObject.value M N S n U u := by
      funext j
      exact (rv_normalize _).symm.trans (congrFun hp j)
    change AlgebraicAt (B.real ∪ {b | ∃ j : Fin n, j ≠ i ∧ (@rv M sM hM (p.val.1 j)).val = b}) .rv
      (@rv M sM hM (p.val.1 i)).val at ha
    change AlgebraicAt (coordinateBase B.real i (fun j => @rv M sM hM (p.val.1 j))) .rv
      ((fun j => @rv M sM hM (p.val.1 j)) i).val at ha
    rw [he] at ha
    have hNalg := (@algebraicAt_normalize_iff M sM hM _ .rv _).mpr ha
    refine @AlgebraicAt.mono M N _ _ ?_ .rv _ hNalg
    rintro b (hb | hb)
    · exact Or.inl (hBS hb)
    · exact Or.inr hb
  letI := N
  letI := hN
  refine ⟨?_,halg⟩
  intro u he
  exact hnz u (Subtype.ext (he.trans RVOperations.zero_val.symm))

end IntegrationInACVF.Section6
