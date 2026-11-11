import IntegrationSection4.VerticalOffsets

/-! The uniform vertical chart used in Lemma 4.8. The source is arbitrary
original-base definable; the ambient coordinate change and positioning map
are actual original-real-base definable maps. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5

namespace IntegrationInACVF.Section4.VerticalCharts

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Every original-base source admits uniform vertical translated-RV
charts. No family of positioning functions or cell decomposition is an input. -/
theorem exists_chart {κ : Cardinal} (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (G : GammaParameters.Base (M := M)) (hsmall : Cardinal.mk G.real < κ)
    (hGenerated : VFGammaGeneratedBase G) {n m : ℕ}
    (A : Set (Point (M := M) (n+1) m)) (hA : GammaSetDefinable G A) :
    ∃ l : ℕ, ∃ B : DefSet (M := M) G.real (n+1) l,
      ∃ T : RelativeBijection (PresentedSet.univ (pointSpace (n+1) m) G.real) B,
        HeadSaturated (carrier B) ∧ (∃ j, Tagged (carrier B) 0 j) ∧
          let C := {q | ∃ a : PresentedSet.univ (pointSpace (M := M) (n+1) m) G.real,
            a.val ∈ A ∧ (T.toMap a).val = q}
          GammaSetDefinable G C ∧ HeadSaturated C ∧
            ∀ b : B, b.val ∈ C →
              (T.inverseSlice b ⊆ A) ∧
                VerticalOffsets.headBody T b = (fun x => x+VerticalOffsets.offsetValue T (VerticalOffsets.toKey B b)) ''
                  {x : VF (M := M) | rv x = rv (vfAt b.val 0)} := by
  let r : Point (M := M) (n+1) m → Point (M := M) 0 0 → Prop := fun p _ => p ∈ A
  let hΓ := gammaLogicInput G
  have hr : GammaGraphDefinable G r := by
    have h := hΓ.restrict_graph hA (hΓ.real_map_graph
      (constantRVMap (PresentedSet.univ (pointSpace (n+1) m) G.real) 0))
    apply GammaGraphDefinable.congr h
    intro p q
    exact ⟨fun h => h.1,fun hp => ⟨hp,⟨p,Set.mem_univ _⟩,rfl,Subsingleton.elim _ _⟩⟩
  obtain ⟨l,B,T,hB,hTag,hUniform⟩ := RelativeGammaPreparation.prepare hs h00 G hsmall hGenerated r hr
  let C := {q | ∃ a : PresentedSet.univ (pointSpace (M := M) (n+1) m) G.real,
    a.val ∈ A ∧ (T.toMap a).val = q}
  have hC : GammaSetDefinable G C := hΓ.image_real T.toMap hA
  have hInv (b : B) (hb : b.val ∈ C) : (T.inverseMap b).val ∈ A := by
    obtain ⟨a,ha,he⟩ := hb
    have hab : T.toMap a = b := Subtype.ext he
    rwa [← hab,T.inverse_apply]
  have hCHead : HeadSaturated C := by
    rintro p ⟨a,ha,rfl⟩ x hx
    let b := T.toMap a
    let c : B := ⟨replace 0 b.val x,hB b.val b.property x hx⟩
    have he : SameRV b.val c.val := sameRV_replace 0 b.val x hx
    have ht : TailEq b.val c.val := by intro i; simp [c,replace,vfAt,Fin.succ_ne_zero]
    have hh := hUniform b c he ht (Fin.elim0,Fin.elim0)
    change (T.inverseMap b).val ∈ A ↔ (T.inverseMap c).val ∈ A at hh
    have hb : (T.inverseMap b).val ∈ A := by change (T.inverseMap (T.toMap a)).val ∈ A; rwa [T.inverse_apply]
    exact ⟨T.inverseMap c,hh.mp hb,congrArg Subtype.val (T.apply_inverse c)⟩
  refine ⟨l,B,T,hB,hTag,hC,hCHead,?_⟩
  intro b hb
  refine ⟨?_,VerticalOffsets.inverse_head_translate T hB b⟩
  rintro p ⟨a,ha,he,ht⟩
  have hh := hUniform (T.toMap a) b he ht (Fin.elim0,Fin.elim0)
  change (T.inverseMap (T.toMap a)).val ∈ A ↔ (T.inverseMap b).val ∈ A at hh
  rw [T.inverse_apply] at hh
  exact ha ▸ hh.mpr (hInv b hb)

end IntegrationInACVF.Section4.VerticalCharts
