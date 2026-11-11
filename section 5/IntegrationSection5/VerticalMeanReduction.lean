import IntegrationSection5.FibreFocusBoundary

/-! The one-coordinate canonical mean step strictly reduces the number of
nonzero roots in each retained-label fibre. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n m : ℕ} {A : DefSet (M := M) S (n+1) m}

def verticalParentBase (q : Point (M := M) n (1+m)) : Point (M := M) n m :=
  (q.1,fun j => q.2 (Fin.natAdd 1 j))

theorem verticalMeanStep_apply (R : VerticalRootFamily A) (h00 : M ⊨ Axioms.ACVF00)
    (d : ℕ) (hd : R.Bound d) (a : A) :
    (verticalMeanStepMap R h00 d hd a).val = coordinateCanonical 0 (verticalMeanEta R a.val) := rfl

theorem verticalMeanStep_fibre_subset (R : VerticalRootFamily A) (h00 : M ⊨ Axioms.ACVF00)
    (d : ℕ) (hd : R.Bound d) (q : Point (M := M) n (1+m)) (x : VF (M := M))
    (hx : insertHead x q ∈ carrier (R.imageSet (verticalMeanStepMap R h00 d hd))) :
    x ∈ ((R.fibre (verticalParentBase q)).filter
      (fun y => rv (y-Barycentre.mean (R.fibre (verticalParentBase q))) = q.2 (Fin.castAdd m 0))).image
      (fun y => y-Barycentre.mean (R.fibre (verticalParentBase q))) := by
  obtain ⟨a,ha,he⟩ := (R.mem_imageSet _ _).mp hx
  rw [verticalMeanStep_apply] at he
  have hl := R.subset_verticalHull ha
  rw [verticalMeanEta,if_pos hl] at he
  have hBase : dropHead id a.val = verticalParentBase q := by
    refine Prod.ext ?_ ?_
    · funext j
      have h := congrArg (fun p : Point (M := M) (n+1) (1+m) => vfAt p j.succ) he
      simpa only [coordinateCanonical,replace,vfAt,Function.update_of_ne (Fin.succ_ne_zero j),insertHead,verticalParentBase,dropHead,Fin.cons_succ] using h
    · funext j
      have h := congrArg (fun p : Point (M := M) (n+1) (1+m) => p.2 (Fin.natAdd 1 j)) he
      simpa only [coordinateCanonical,Fin.append_right,replace,insertHead,verticalParentBase,dropHead,id_eq] using h
  have hHead : vfAt a.val 0-verticalMeanCentre R a.val = x := by
    have h := congrArg (fun p : Point (M := M) (n+1) (1+m) => vfAt p 0) he
    simpa only [coordinateCanonical,replace,vfAt,Function.update_self,insertHead,Fin.cons_zero] using h
  have hc : verticalMeanCentre R a.val = Barycentre.mean (R.fibre (verticalParentBase q)) :=
    congrArg (fun b => Barycentre.mean (R.fibre b)) hBase
  refine Finset.mem_image.mpr ⟨vfAt a.val 0,Finset.mem_filter.mpr ⟨?_,?_⟩,?_⟩
  · apply (R.mem_fibre _ _).mpr
    rw [← hBase,insertHead_dropHead]
    exact ha
  · have h := congrArg (fun p : Point (M := M) (n+1) (1+m) => p.2 (Fin.castAdd m 0)) he
    change rv (vfAt a.val 0-verticalMeanCentre R a.val) = q.2 (Fin.castAdd m 0) at h
    rwa [hc] at h
  · rwa [hc] at hHead

def verticalMeanStepFamily (R : VerticalRootFamily A) (h00 : M ⊨ Axioms.ACVF00)
    (d : ℕ) (hd : R.Bound d) : VerticalRootFamily (verticalMeanStepTarget R h00 d hd) where
  set := R.imageSet (verticalMeanStepMap R h00 d hd)
  subset := R.imageSet_subset _
  finite q := by
    let F := R.fibre (verticalParentBase q)
    let U := (F.filter (fun y => rv (y-Barycentre.mean F) = q.2 (Fin.castAdd m 0))).image
      (fun y => y-Barycentre.mean F)
    exact U.finite_toSet.subset (fun x hx => verticalMeanStep_fibre_subset R h00 d hd q x hx)

theorem verticalMeanStep_bound (R : VerticalRootFamily A) (h00 : M ⊨ Axioms.ACVF00)
    (d : ℕ) (hd : R.Bound (d+1)) : (verticalMeanStepFamily R h00 (d+1) hd).Bound d := by
  intro q hne
  apply finite_mean_child_bound h00 (R.fibre (verticalParentBase q))
    ((verticalMeanStepFamily R h00 (d+1) hd).fibre q) (q.2 (Fin.castAdd m 0)) d (hd _)
  · intro x hx
    exact verticalMeanStep_fibre_subset R h00 (d+1) hd q x
      (((verticalMeanStepFamily R h00 (d+1) hd).mem_fibre q x).mp hx)
  · exact hne

/-- Uniform root centering by actual relatively special bijections. Every
fibre chain begins legally after a canonical step and ends canonically. -/
theorem verticalRoots_centralize (h00 : M ⊨ Axioms.ACVF00) (d : ℕ) :
    ∀ {m : ℕ} (A : DefSet (M := M) S (n+1) m) (R : VerticalRootFamily A),
      HeadSaturated (carrier A) → (∃ k, Tagged (carrier A) 0 k) → R.Bound d →
      ∃ l, ∃ B : DefSet (M := M) S (n+1) l, ∃ f : Map A B,
        SpecialRelativeBoundary f 0 (some false) (some false) ∧
          HeadSaturated (carrier B) ∧ (∃ k, Tagged (carrier B) 0 k) ∧
            ∀ a : A, a.val ∈ carrier R.set → vfAt (f a).val 0 = 0 := by
  induction d with
  | zero =>
    intro m A R hA hTag hd
    exact ⟨m,A,Map.id A,specialRelativeBoundary_id A 0 (some false),hA,hTag,
      fun a ha => R.bound_zero hd a.val ha⟩
  | succ d ih =>
    intro m A R hA hTag hd
    obtain ⟨k,hk⟩ := hTag
    let f := verticalMeanStepMap R h00 (d+1) hd
    let Q := verticalMeanStepFamily R h00 (d+1) hd
    have hf := verticalMeanStep_boundary R h00 (d+1) hd hk
    have hSat := verticalMeanStep_headSaturated R h00 (d+1) hd hk hA
    have hTag' : ∃ k, Tagged (carrier (verticalMeanStepTarget R h00 (d+1) hd)) 0 k :=
      ⟨Fin.castAdd _ 0,coordinateCanonical_tagged _ 0⟩
    obtain ⟨l,B,g,hg,hB,hTagB,hz⟩ := ih _ Q hSat hTag' (verticalMeanStep_bound R h00 d hd)
    refine ⟨l,B,Map.comp g f,specialRelativeBoundary_comp f g 0 hf hg,hB,hTagB,?_⟩
    intro a ha
    apply hz (f a)
    exact (R.mem_imageSet f _).mpr ⟨a,ha,rfl⟩

end IntegrationInACVF.Section5
