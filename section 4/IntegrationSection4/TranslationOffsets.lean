import IntegrationSection4.DefinableDescent
import Section5.TransformGeometry

/-! Lemma 4.1, real-parameter version. We reuse the predecessor's actual
special bijections and difference-preservation theorem. No RV representatives
are added to the parameter base. The absorbing RV fibre is included. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section4.TranslationOffsets

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {m l : ℕ}
variable {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 l}

def labelsMap (B : DefSet (M := M) S 1 l) :
    Map B (PresentedSet.univ (SpecialTransformations.Section4.rvSpace l) S) :=
  @SpecialTransformations.DefinableGeometry.Map.snd LRV M (CanonicalStructure.normalize (M := M))
    (SpecialTransformations.Section4.vfSpace 1)
    (SpecialTransformations.Section4.rvSpace l) S B

def labelsImage (B : DefSet (M := M) S 1 l) :=
  Map.image (labelsMap B)

def toLabels (B : DefSet (M := M) S 1 l) : B → labelsImage B :=
  Map.toImage (labelsMap B)

theorem inverse_sub (T : SpecialBijection A B) (a b : B)
    (he : a.val.2 = b.val.2) :
    vfAt (T.inverseMap a).val 0 - vfAt (T.inverseMap b).val 0 =
      vfAt a.val 0 - vfAt b.val 0 := by
  have hh := T.chain.unary_sub (T.inverseMap a) (T.inverseMap b) (by
    change (T.toMap (T.inverseMap a)).val.2 = (T.toMap (T.inverseMap b)).val.2
    simpa only [T.apply_inverse] using he)
  change vfAt (T.toMap (T.inverseMap a)).val 0 -
    vfAt (T.toMap (T.inverseMap b)).val 0 = _ at hh
  simpa only [T.apply_inverse] using hh.symm

def displacementMap (T : SpecialBijection A B) :
    Map B (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) S) := by
  let own := @SpecialTransformations.DefinableGeometry.Map.fst LRV M (CanonicalStructure.normalize (M := M))
    (SpecialTransformations.Section4.vfSpace 1)
    (SpecialTransformations.Section4.rvSpace l) S B
  let paired := Map.pair T.inverseMap own
  let subtracted := Map.comp (subtractMap 0 _) paired
  exact Map.comp (@SpecialTransformations.DefinableGeometry.Map.fst LRV M (CanonicalStructure.normalize (M := M))
    (SpecialTransformations.Section4.vfSpace 1)
    (SpecialTransformations.Section4.rvSpace m) S _) subtracted

theorem displacementMap_apply (T : SpecialBijection A B) (b : B) :
    (displacementMap T b).val 0 =
      vfAt (T.inverseMap b).val 0 - vfAt b.val 0 := by
  rfl

theorem displacement_constant (T : SpecialBijection A B) (a b : B)
    (he : labelsMap B a = labelsMap B b) : displacementMap T a = displacementMap T b := by
  apply Subtype.ext
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  rw [displacementMap_apply, displacementMap_apply]
  have hd := inverse_sub T a b (congrArg Subtype.val he)
  linear_combination hd

def offsetMap (T : SpecialBijection A B) :
    Map (labelsImage B) (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) S) :=
  @DefinableDescent.descendMap LRV M (CanonicalStructure.normalize (M := M))
    _ _ _ S _ _ _ (labelsMap B) (displacementMap T) (displacement_constant T)

def offsetValue (T : SpecialBijection A B) (u : labelsImage B) : VF (M := M) :=
  (offsetMap T u).val 0

theorem offsetValue_eq (T : SpecialBijection A B) (b : B) :
    offsetValue T (toLabels B b) = vfAt (T.inverseMap b).val 0 - vfAt b.val 0 := by
  have he := @DefinableDescent.descendMap_spec LRV M (CanonicalStructure.normalize (M := M))
    _ _ _ S _ _ _ (labelsMap B) (displacementMap T) (displacement_constant T) b
  exact (congrArg (fun z => (show VF (M := M) from z.val 0)) he).trans (displacementMap_apply T b)

theorem offsetMap_spec (T : SpecialBijection A B) (b : B) :
    vfAt (T.inverseMap b).val 0 =
      vfAt b.val 0 + offsetValue T (toLabels B b) := by
  have he := @DefinableDescent.descendMap_spec LRV M (CanonicalStructure.normalize (M := M))
    _ _ _ S _ _ _
    (labelsMap B) (displacementMap T) (displacement_constant T) b
  have hv := congrArg (fun z => (show VF (M := M) from z.val 0)) he
  change offsetValue T (toLabels B b) = (show VF (M := M) from (displacementMap T b).val 0) at hv
  rw [hv, displacementMap_apply]
  rw [add_comm (vfAt b.val 0)]
  exact (sub_add_cancel _ _).symm

/-- The full inverse RV-fibre formula, including the degenerate zero fibre.
The compatible target point supplies the leading term and the RV labels. -/
theorem inverse_fibre_translate (T : SpecialBijection A B)
    (hB : IsRVPullback (carrier B)) (b : B) :
    (fun p : Point (M := M) 1 m => vfAt p 0) '' T.inverseFibre b =
      (fun x => x + offsetValue T (toLabels B b)) ''
        {x : VF (M := M) | rv x = rv (vfAt b.val 0)} := by
  ext z
  constructor
  · rintro ⟨p, ⟨a, rfl, ha⟩, rfl⟩
    have hh := (sameRV_iff _ _).mp ha
    refine ⟨vfAt (T.toMap a).val 0, hh.1 0, ?_⟩
    have hl : toLabels B (T.toMap a) = toLabels B b := Subtype.ext hh.2
    have hs := offsetMap_spec T (T.toMap a)
    rw [T.inverse_apply, hl] at hs
    exact hs.symm
  · rintro ⟨x, hx, rfl⟩
    let p : Point (M := M) 1 l := (![x], b.val.2)
    have hp : SameRV b.val p := (sameRV_iff _ _).mpr ⟨by
      intro i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact hx.symm, rfl⟩
    have hpB : p ∈ carrier B := (@isRVPullback_iff M sM hM 1 l (carrier B)).mp hB b.val b.property p hp
    let c : B := ⟨p, hpB⟩
    refine ⟨(T.inverseMap c).val, ⟨T.inverseMap c, rfl, ?_⟩, ?_⟩
    · rw [T.apply_inverse]
      exact hp.symm
    · have hl : toLabels B c = toLabels B b := Subtype.ext rfl
      have hs := offsetMap_spec T c
      rw [hl] at hs
      exact hs

/-- Lemma 4.1 over an arbitrary real parameter set, with the full definable
offset graph and the actual inverse VF images. Named Gamma descent is a
separate obligation, not a hidden input to this result. -/
theorem lemma_4_1_real_base (T : SpecialBijection A B)
    (hB : IsRVPullback (carrier B)) :
    ∃ ε : Map (labelsImage B)
        (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) S),
      ∀ b : B,
        (fun p : Point (M := M) 1 m => vfAt p 0) '' T.inverseFibre b =
          (fun x : VF (M := M) => x + (show VF (M := M) from (ε (toLabels B b)).val 0)) ''
            {x : VF (M := M) | rv x = rv (vfAt b.val 0)} :=
  ⟨offsetMap T, inverse_fibre_translate T hB⟩

end IntegrationInACVF.Section4.TranslationOffsets
