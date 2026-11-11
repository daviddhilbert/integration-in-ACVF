import IntegrationSection4.VerticalMeanStep
import Section5.Assembly

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section4.RelativeRootReduction

open VerticalMeanStep

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m : ℕ} {A : DefSet (M := M) S (n+1) m}

theorem canonical_headSaturated (A : DefSet (M := M) S (n+1) m)
    (hA : HeadSaturated (carrier A)) : HeadSaturated (carrier (canonicalImage A)) := by
  rintro p ⟨a,rfl⟩ x hx
  change rv x = rv (vfAt a.val 0) at hx
  refine ⟨⟨replace 0 a.val x,hA a.val a.property x hx⟩,?_⟩
  change canonical (replace 0 a.val x) = replace 0 (canonical a.val) x
  apply Prod.ext
  · rfl
  · funext i
    cases i using Fin.addCases with
    | left j =>
      cases j using Fin.cases with
      | zero => exact hx
      | succ j => simp [canonical,replace,vfAt,Fin.succ_ne_zero]
    | right j => simp only [canonical_old,replace]

theorem step_fibre_subset (R : VerticalRootFamily A) (h00 : M ⊨ Axioms.ACVF00) (N : ℕ)
    (hN : ∀ p, (R.fibre p).card ≤ N) (k : Fin m) (hTag : Tagged (carrier A) 0 k)
    (q : Point (M := M) n ((n+1)+m)) (x : VF (M := M))
    (hx : insertHead x q ∈ carrier (R.imageSet (step R h00 N hN k hTag).toMap)) :
    x ∈ ((R.fibre (VerticalRootFamily.parentBase q)).filter
      (fun y => rv (y-Barycentre.mean (R.fibre (VerticalRootFamily.parentBase q))) =
        q.2 (Fin.castAdd m (0 : Fin (n+1))))).image
      (fun y => y-Barycentre.mean (R.fibre (VerticalRootFamily.parentBase q))) := by
  obtain ⟨a,ha,he⟩ := (R.mem_imageSet _ _).mp hx
  rw [step_apply] at he
  have hBase : dropHead id a.val = VerticalRootFamily.parentBase q := by
    apply Prod.ext
    · funext i
      have hh := congrArg (fun p : Point (M := M) (n+1) ((n+1)+m) => vfAt p i.succ) he
      change vfAt (eta R a.val) i.succ = vfAt (insertHead x q) i.succ at hh
      change vfAt a.val i.succ = vfAt q i
      simpa [eta,replace,vfAt,insertHead,Fin.succ_ne_zero] using hh
    · funext i
      have hh := congrArg (fun p : Point (M := M) (n+1) ((n+1)+m) => p.2 (Fin.natAdd (n+1) i)) he
      change a.val.2 i = q.2 (Fin.natAdd (n+1) i)
      simpa only [canonical_old,eta,replace,insertHead] using hh
  have hHead : vfAt a.val 0-centre R a.val = x := by
    have hh := congrArg (fun p : Point (M := M) (n+1) ((n+1)+m) => vfAt p 0) he
    exact hh
  have hc : centre R a.val = Barycentre.mean (R.fibre (VerticalRootFamily.parentBase q)) :=
    congrArg (fun b => Barycentre.mean (R.fibre b)) hBase
  refine Finset.mem_image.mpr ⟨vfAt a.val 0,Finset.mem_filter.mpr ⟨?_,?_⟩,?_⟩
  · apply (R.mem_fibre _ _).mpr
    rw [← hBase,insertHead_dropHead]
    exact ha
  · have hh := (canonical_new (eta R a.val) (0 : Fin (n+1))).symm.trans
      (congrArg (fun p : Point (M := M) (n+1) ((n+1)+m) => p.2 (Fin.castAdd m 0)) he)
    change rv (vfAt a.val 0-centre R a.val) = q.2 (Fin.castAdd m 0) at hh
    rwa [hc] at hh
  · rwa [hc] at hHead

def stepFamily (R : VerticalRootFamily A) (h00 : M ⊨ Axioms.ACVF00) (N : ℕ)
    (hN : ∀ p, (R.fibre p).card ≤ N) (k : Fin m) (hTag : Tagged (carrier A) 0 k) :
    VerticalRootFamily (canonicalImage (etaImage R h00 N hN)) where
  set := R.imageSet (step R h00 N hN k hTag).toMap
  subset := R.imageSet_subset _
  finite q := by
    let F := R.fibre (VerticalRootFamily.parentBase q)
    let U := (F.filter (fun y => rv (y-Barycentre.mean F) = q.2 (Fin.castAdd m 0))).image
      (fun y => y-Barycentre.mean F)
    exact U.finite_toSet.subset (fun x hx => step_fibre_subset R h00 N hN k hTag q x hx)

theorem step_bound (R : VerticalRootFamily A) (h00 : M ⊨ Axioms.ACVF00) (N : ℕ)
    (hN : ∀ p, (R.fibre p).card ≤ N) (k : Fin m) (hTag : Tagged (carrier A) 0 k)
    (d : ℕ) (hd : R.Bound (d+1)) : (stepFamily R h00 N hN k hTag).Bound d := by
  intro q hne
  apply finite_mean_child_bound h00 (R.fibre (VerticalRootFamily.parentBase q))
    ((stepFamily R h00 N hN k hTag).fibre q) (q.2 (Fin.castAdd m 0)) d (hd _)
  · intro x hx
    exact step_fibre_subset R h00 N hN k hTag q x
      (((stepFamily R h00 N hN k hTag).mem_fibre q x).mp hx)
  · exact hne

/-- All root-count reductions are vertical: the complementary VF tuple is
fixed throughout the actual definable bijection. -/
theorem centralize (h00 : M ⊨ Axioms.ACVF00) (d : ℕ) :
    ∀ {m : ℕ} (A : DefSet (M := M) S (n+1) m) (R : VerticalRootFamily A),
      HeadSaturated (carrier A) → (∃ k, Tagged (carrier A) 0 k) → R.Bound d →
      ∃ l : ℕ, ∃ B : DefSet (M := M) S (n+1) l, ∃ T : RelativeBijection A B,
        HeadSaturated (carrier B) ∧ (∃ k, Tagged (carrier B) 0 k) ∧
          ∀ a : A, a.val ∈ carrier R.set → vfAt (T.toMap a).val 0 = 0 := by
  induction d with
  | zero =>
    intro m A R hA hTag hd
    exact ⟨m,A,RelativeBijection.refl A,hA,hTag,fun a ha => R.bound_zero hd a.val ha⟩
  | succ d ih =>
    intro m A R hA hTag hd
    obtain ⟨k,hk⟩ := hTag
    let N := d+2
    have hN : ∀ p, (R.fibre p).card ≤ N := R.card_bound (d+1) hd
    let T := step R h00 N hN k hk
    let Q := stepFamily R h00 N hN k hk
    have hQ := step_bound R h00 N hN k hk d hd
    have hB : HeadSaturated (carrier (canonicalImage (etaImage R h00 N hN))) :=
      canonical_headSaturated _ (etaImage_headSaturated R h00 N hN k hk hA)
    have hTagged : ∃ j, Tagged (carrier (canonicalImage (etaImage R h00 N hN))) 0 j :=
      canonicalImage_allTagged _ 0
    obtain ⟨l,B,U,hSat,hTagB,hz⟩ := ih _ Q hB hTagged hQ
    refine ⟨l,B,T.comp U,hSat,hTagB,?_⟩
    intro a ha
    apply hz (T.toMap a)
    exact (R.mem_imageSet T.toMap _).mpr ⟨a,ha,rfl⟩

end IntegrationInACVF.Section4.RelativeRootReduction
