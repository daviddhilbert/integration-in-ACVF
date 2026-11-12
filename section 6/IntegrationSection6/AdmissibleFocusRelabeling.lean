import IntegrationSection6.BlowupCoordinateFormula

/-! The relabeling part of6.12 needs no bound on the presentation code set:
admissibility is already an input to an elementary blowup. This matters
for genuine original-Gamma objects whose real code presentation may be large. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
namespace IntegrationInACVF.Section6
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n : ℕ} {U : RVObject (M := M) S n}
variable {i : Fin n}

theorem Admissible.rv_nonzero (h : Admissible U i) (u : U.domain) : U.value u i ≠ 0 := by
  intro he
  exact h.nonzero u ((congrArg Subtype.val he).trans RVOperations.zero_val)

variable {A : SpecialTransformations.Section5.DefSet (M := M) S n U.arity}
variable (h : PresentsLift U A) {k : Fin U.arity}
variable (D : SpecialTransformations.Section5.Focus A i k)
variable (hfull : SpecialTransformations.Section5.carrier A ⊆ D.locus)
variable (hAd : Admissible U i)

/-- The image calculation and an already admissible coordinate give the
blowup isomorphism without an extra saturation or small-code hypothesis. -/
def admissibleFullFocusBlowup :
    ElementaryBlowup U (fullFocusObject h D hfull hAd.rv_nonzero) where
  coordinate := i
  admissible := hAd
  iso := (fullFocusObjectKeyIso h D hfull hAd.rv_nonzero).trans
    (elementaryKeyIso U i hAd).symm

theorem admissibleFullFocusBlowup_volume
    (a : (fullFocusObject h D hfull hAd.rv_nonzero).domain) :
    (elementary U i).value ((admissibleFullFocusBlowup h D hfull hAd).iso.hom.map a) =
      (fullFocusObject h D hfull hAd.rv_nonzero).value a := by
  change (elementary U i).value ((elementaryKeyIso U i hAd).inv.map
    ((fullFocusObjectKeyIso h D hfull hAd.rv_nonzero).hom.map a)) = _
  exact elementaryKeyIso_inv_volume U i hAd
    ((fullFocusObjectKeyIso h D hfull hAd.rv_nonzero).hom.map a)

/-- A genuine full-graph definable bijection, fixing every VF coordinate. -/
def admissibleFocusRelabelLift :=
  volumePreservingLiftMap (admissibleFullFocusBlowup h D hfull hAd).iso.hom.map
    (admissibleFullFocusBlowup_volume h D hfull hAd)

theorem admissibleFocusRelabelLift_bijective :
    Function.Bijective (admissibleFocusRelabelLift h D hfull hAd) :=
  volumePreservingLiftMap_bijective _ _
    (iso_map_bijective (admissibleFullFocusBlowup h D hfull hAd).iso)

@[simp] theorem admissibleFocusRelabelLift_vf
    (a : rvLift (fullFocusObject h D hfull hAd.rv_nonzero)) :
    (admissibleFocusRelabelLift h D hfull hAd a).val.1 = a.val.1 := rfl

@[simp] theorem admissibleFocusRelabelLift_square
    (a : rvLift (fullFocusObject h D hfull hAd.rv_nonzero)) :
    (admissibleFocusRelabelLift h D hfull hAd a).val.2 =
      ((admissibleFullFocusBlowup h D hfull hAd).iso.hom.map
        (liftLabelProjection (fullFocusObject h D hfull hAd.rv_nonzero) a)).val := rfl

theorem admissibleFocusRelabelLift_parameter
    (a : rvLift (fullFocusObject h D hfull hAd.rv_nonzero)) :
    let b := admissibleFocusRelabelLift h D hfull hAd a
    (elementaryParameter U i (liftLabelProjection (elementary U i) b)).val 0 =
      tupleRV a.val.1 i /
        U.value (elementaryProjection U i (liftLabelProjection (elementary U i) b)) i := by
  have he := elementaryLift_parameter U i hAd.rv_nonzero (admissibleFocusRelabelLift h D hfull hAd a)
  rw [admissibleFocusRelabelLift_vf] at he
  exact he

end IntegrationInACVF.Section6
