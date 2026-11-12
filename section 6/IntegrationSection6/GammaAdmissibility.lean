import IntegrationSection6.AlgebraicFibres
import Section7.GammaVolumeCorrespondence
import Section3.RVGammaAlgebraicity
import Section3.SmallFiniteParameters

/-! Admissibility over the original real/Gamma base, with a bridge to the
actual normalized RV object. The internal code set need not be small. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7

namespace IntegrationInACVF.Section6

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {k : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

structure GammaAdmissible (U : GammaRVObject B k) (i : Fin k) : Prop where
  nonzero : ∀ u : rvObjectDomain U.object, (gammaVolumeValue U u i).val ≠ iRVZero
  algebraic : ∀ u : rvObjectDomain U.object,
    AlgebraicAtBase ⟨coordinateBase B.real i (gammaVolumeValue U u),B.gamma⟩
      .rv (gammaVolumeValue U u i).val

/-- Algebraicity is valid in the released normalized real presentation;
only the original real base, enlarged by finitely many labels, is bounded. -/
theorem GammaAdmissible.ordinary {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)
    {U : GammaRVObject B k} {i : Fin k} (h : GammaAdmissible U i) :
    @Admissible M (@CanonicalStructure.normalize M sM)
      (@GammaRVObject.codes M sM hM B k U) k
      (@GammaRVObject.object M sM hM B k U) i := by
  refine @Admissible.mk M N _ k _ i ?_ ?_
  · intro u
    have he := @CanonicalStructure.normalize_fun M sM 0 Fn.rvZero Fin.elim0 (fun j => j.elim0)
    change (gammaVolumeValue U u i).val ≠ @iRVZero M N
    change @iRVZero M N = @iRVZero M sM at he
    exact fun hz => h.nonzero u (hz.trans he)
  · intro u
    let t := gammaVolumeValue U u
    have hsmall' : Cardinal.mk (coordinateBase B.real i t) < κ := by
      apply (Cardinal.mk_le_mk_of_subset (show coordinateBase B.real i t ⊆
        B.real ∪ Set.range (fun j => (t j).val) from ?_)).trans_lt
          (small_union_range hκ B.real hsmall _)
      rintro x (hx | ⟨j,_,rfl⟩)
      · exact Or.inl hx
      · exact Or.inr (Set.mem_range_self j)
    have hr := (algebraic_rv_gamma_base_iff hκ hs h00
      ⟨coordinateBase B.real i t,B.gamma⟩ hsmall' (t i).val).mp (h.algebraic u)
    have hn := (@algebraicAt_normalize_iff M sM hM _ .rv _).mpr hr
    refine @AlgebraicAt.mono M N _ _ ?_ .rv _ hn
    rintro x (hx | hx)
    · exact Or.inl (U.real_contains hx)
    · exact Or.inr hx

end IntegrationInACVF.Section6
