import IntegrationSection4.RelativeSlices
import Section5.VerticalObstacles
import Section3.GammaValueLaws

/-! Root-free vertical relation preparation. The zero-obstacle argument is
adapted from Special transformations, Section5/Assembly.lean, revision
9cc9760892092dd34cfad4a6dee655843c52f30c, to actual relative bijections and
head-saturated targets. All obstacle and map-existence premises are discharged
by checked root families and the vertical mean reduction below. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section4.RelativeObstaclePreparation

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m l k : ℕ}
variable {A : DefSet (M := M) S (n+1) m} {B : DefSet (M := M) S (n+1) l}

theorem zero_obstacles {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VF (M := M)) Γ)
    (hv : ∀ x y : VF (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (U : Set (Point (M := M) (n + 1) k)) (R : VerticalRootFamily A)
    (hO : ∀ (p : Point (M := M) n m) (a : VF (M := M)) (r : SpecialTransformations.Section3.Balls.Radius Γ),
      (∀ x ∈ SpecialTransformations.Section3.Balls.openDisc v a r, insertHead x p ∈ carrier A) →
      (∀ x ∈ R.fibre p, x ∉ SpecialTransformations.Section3.Balls.openDisc v a r) →
      ∀ x ∈ SpecialTransformations.Section3.Balls.openDisc v a r, ∀ y ∈ SpecialTransformations.Section3.Balls.openDisc v a r,
      ∀ ys : Fin k → RV (M := M),
        (((insertHead x p).1, ys) ∈ U ↔ ((insertHead y p).1, ys) ∈ U))
    (T : RelativeBijection A B) (hB : HeadSaturated (carrier B))
    (hz : ∀ a : A, a.val ∈ carrier R.set → vfAt (T.toMap a).val 0 = 0) :
    ∀ b c : B, SameRV b.val c.val → TailEq b.val c.val →
      ∀ ys : Fin k → RV (M := M),
        (((T.inverseMap b).val.1,ys) ∈ U ↔ ((T.inverseMap c).val.1,ys) ∈ U) := by
  intro b c hbc htail ys
  obtain ⟨hrv, hlabels⟩ := (sameRV_iff _ _).mp hbc
  by_cases hb : vfAt b.val 0 = 0
  · have hc : vfAt c.val 0 = 0 := (rv_eq_zero_iff _).mp ((hrv 0).symm.trans (congrArg rv hb))
    have he : b = c := by
      apply Subtype.ext
      refine Prod.ext ?_ hlabels
      funext i
      cases i using Fin.cases with
      | zero => exact hb.trans hc.symm
      | succ i => exact htail i
    subst c
    rfl
  · obtain ⟨he, _⟩ := T.inverse_slice v hv hB b hb
    let a₀ := T.inverseMap b
    let p := dropHead id a₀.val
    let centre := vfAt a₀.val 0
    let ρ : SpecialTransformations.Section3.Balls.Radius Γ := ↑(OrderDual.toDual (v (vfAt b.val 0)))
    have hrad : v (vfAt b.val 0) ≠ 0 := (map_ne_zero v).mpr hb
    have hmem (x : VF (M := M)) (hx : x ∈ SpecialTransformations.Section3.Balls.openDisc v centre ρ) :
        insertHead x p ∈ T.inverseSlice b := by
      rw [he]
      refine ⟨?_, (fun _ => rfl), rfl⟩
      change v (x - centre) < v (vfAt b.val 0)
      simpa only [SpecialTransformations.Section3.Balls.openDisc, ρ, OrderDual.ofDual_toDual, if_neg hrad,
        Set.mem_ofPred_eq] using hx
    have hball : ∀ x ∈ SpecialTransformations.Section3.Balls.openDisc v centre ρ, insertHead x p ∈ carrier A := by
      intro x hx
      obtain ⟨a, ha, _, _⟩ := hmem x hx
      exact ha ▸ a.property
    have havoid : ∀ x ∈ R.fibre p, x ∉ SpecialTransformations.Section3.Balls.openDisc v centre ρ := by
      intro x hx hxd
      obtain ⟨a, ha, hrv, _⟩ := hmem x hxd
      have hroot : a.val ∈ carrier R.set := ha.symm ▸ (R.mem_fibre p x).mp hx
      have hzero := hz a hroot
      have hh := ((sameRV_iff _ _).mp hrv).1 0
      change rv (vfAt (T.toMap a).val 0) = rv (vfAt b.val 0) at hh
      exact hb ((rv_eq_zero_iff _).mp (hh.symm.trans (congrArg rv hzero)))
    have hcF : (T.inverseMap c).val ∈ T.inverseSlice b :=
      ⟨T.inverseMap c, rfl, by rw [T.apply_inverse]; exact hbc.symm,
        by rw [T.apply_inverse]; intro i; exact (htail i).symm⟩
    rw [he] at hcF
    have hy : vfAt (T.inverseMap c).val 0 ∈ SpecialTransformations.Section3.Balls.openDisc v centre ρ := by
      simpa only [SpecialTransformations.Section3.Balls.openDisc, ρ, OrderDual.ofDual_toDual, if_neg hrad,
        Set.mem_ofPred_eq] using hcF.1
    have hpC : dropHead id (T.inverseMap c).val = p := Prod.ext (funext hcF.2.1) hcF.2.2
    have hOrigB : insertHead centre p = a₀.val := insertHead_dropHead a₀.val
    have hOrigC : insertHead (vfAt (T.inverseMap c).val 0) p = (T.inverseMap c).val := by
      rw [← hpC, insertHead_dropHead]
    have hh := hO p centre ρ hball havoid centre (SpecialTransformations.Section3.Balls.centre_mem_openDisc v centre ρ)
      (vfAt (T.inverseMap c).val 0) hy ys
    rw [hOrigB, hOrigC] at hh
    exact hh


/-- Prepare a real-base RV-valued map in the head direction, leaving every
other VF coordinate fixed. -/
theorem prepare {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (h00 : M ⊨ Axioms.ACVF00) (A : DefSet (M := M) S (n+1) m)
    (hA : IsRVPullback (carrier A)) (hTag : ∃ j, Tagged (carrier A) 0 j)
    (f : Map A (PresentedSet.univ (pointSpace (M := M) 0 k) S)) :
    ∃ l : ℕ, ∃ B : DefSet (M := M) S (n+1) l, ∃ T : RelativeBijection A B,
      HeadSaturated (carrier B) ∧ (∃ j, Tagged (carrier B) 0 j) ∧ ∀ b c : B, SameRV b.val c.val → TailEq b.val c.val →
        f (T.inverseMap b) = f (T.inverseMap c) := by
  let v := Values.presentationValuation (M := M)
  have hv := Values.presentation_compatible (M := M)
  obtain ⟨R,d,hd,hO⟩ := uniformVerticalObstacles hs hsmall v hv n (rvGraph f) A hA
  obtain ⟨l,B,T,hB,hTagged,hz⟩ := RelativeRootReduction.centralize h00 d A R
    (headSaturated_of_pullback hA) hTag hd
  have hRel := zero_obstacles v hv (carrier (rvGraph f)) R hO T hB hz
  refine ⟨l,B,T,hB,hTagged,?_⟩
  intro b c he ht
  let a := T.inverseMap b
  let a' := T.inverseMap c
  have hLabels : a.val.2 = a'.val.2 := T.inverse_labels b c ((sameRV_iff _ _).mp he).2
  let ys := Fin.append a.val.2 (f a).val.2
  have hbG : (a.val.1,ys) ∈ carrier (rvGraph f) := (mem_rvGraph f a.val (f a).val.2).mpr ⟨a,rfl,rfl⟩
  have hcG := (hRel b c he ht ys).mp hbG
  change (a'.val.1,Fin.append a.val.2 (f a).val.2) ∈ carrier (rvGraph f) at hcG
  rw [hLabels] at hcG
  obtain ⟨a'',ha'',hf⟩ := (mem_rvGraph f a'.val (f a).val.2).mp hcG
  have haa : a'' = a' := Subtype.ext ha''
  apply Subtype.ext
  apply Prod.ext
  · exact Subsingleton.elim _ _
  · exact hf.symm.trans (congrArg (fun x : A => (f x).val.2) haa)

end IntegrationInACVF.Section4.RelativeObstaclePreparation
