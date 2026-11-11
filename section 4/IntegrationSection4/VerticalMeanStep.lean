import IntegrationSection4.RelativeBijection
import Section5.RootConstruction

/-! A definable vertical mean step, fixing every complementary VF
coordinate. The root locus need only be saturated in the head coordinate;
no preparation in the complementary coordinates is assumed. -/

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

namespace IntegrationInACVF.Section4.VerticalMeanStep

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m : ℕ} {A : DefSet (M := M) S (n+1) m}

def centre (R : VerticalRootFamily A) (p : Point (M := M) (n+1) m) : VF (M := M) :=
  Barycentre.mean (R.fibre (dropHead id p))

def eta (R : VerticalRootFamily A) (p : Point (M := M) (n+1) m) : Point (M := M) (n+1) m :=
  replace 0 p (vfAt p 0 - centre R p)

@[simp] theorem dropHead_eta (R : VerticalRootFamily A) (p : Point (M := M) (n+1) m) :
    dropHead id (eta R p) = dropHead id p := dropHead_replace_zero _ _ _

def etaMap (R : VerticalRootFamily A) (h00 : M ⊨ Axioms.ACVF00) (N : ℕ)
    (hN : ∀ p, (R.fibre p).card ≤ N) :
    Map A (PresentedSet.univ (pointSpace (n+1) m) S) :=
  Map.comp (subtractMap 0 _) (Map.pair (Map.id A) (R.meanMap h00 N hN A))

@[simp] theorem etaMap_apply (R : VerticalRootFamily A) (h00 : M ⊨ Axioms.ACVF00) (N : ℕ)
    (hN : ∀ p, (R.fibre p).card ≤ N) (p : A) : (etaMap R h00 N hN p).val = eta R p.val := rfl

theorem eta_injective (R : VerticalRootFamily A) (p q : Point (M := M) (n+1) m)
    (he : eta R p = eta R q) : p = q := by
  have hBase := congrArg (dropHead (n := n) id) he
  rw [dropHead_eta,dropHead_eta] at hBase
  have hCentre : centre R p = centre R q := congrArg (fun b => Barycentre.mean (R.fibre b)) hBase
  have hHead := congrArg (fun p : Point (M := M) (n+1) m => vfAt p 0) he
  change vfAt p 0 - centre R p = vfAt q 0 - centre R q at hHead
  rw [hCentre] at hHead
  have h0 : vfAt p 0 = vfAt q 0 := sub_left_inj.mp hHead
  apply Prod.ext
  · funext i
    cases i using Fin.cases with
    | zero => exact h0
    | succ i => exact congrArg (fun z : Point (M := M) n m => vfAt z i) hBase
  · exact congrArg (fun z : Point (M := M) n m => z.2) hBase

def etaImage (R : VerticalRootFamily A) (h00 : M ⊨ Axioms.ACVF00) (N : ℕ)
    (hN : ∀ p, (R.fibre p).card ≤ N) := Map.image (etaMap R h00 N hN)

def step (R : VerticalRootFamily A) (h00 : M ⊨ Axioms.ACVF00) (N : ℕ)
    (hN : ∀ p, (R.fibre p).card ≤ N) (k : Fin m) (hTag : Tagged (carrier A) 0 k) :
    RelativeBijection A (canonicalImage (etaImage R h00 N hN)) where
  toMap := Map.comp (SpecialBijection.canonical (etaImage R h00 N hN)).toMap
    (Map.toImage (etaMap R h00 N hN))
  bijective := by
    constructor
    · intro p q he
      apply Subtype.ext
      apply eta_injective R
      exact canonical_injective (congrArg Subtype.val he)
    · intro b
      obtain ⟨e,he⟩ := (SpecialBijection.canonical (etaImage R h00 N hN)).bijective.2 b
      obtain ⟨a,ha⟩ := e.property
      have he' : Map.toImage (etaMap R h00 N hN) a = e := Subtype.ext ha
      exact ⟨a,by change (SpecialBijection.canonical _).toMap _ = b; rw [he']; exact he⟩
  tail p i := by simp only [eta,replace,vfAt,Function.update_of_ne (Fin.succ_ne_zero i)]; rfl
  labels p q he := by
    funext i
    have hh := congrFun he (Fin.natAdd (n+1) i)
    change (canonical (eta R p.val)).2 (Fin.natAdd (n+1) i) =
      (canonical (eta R q.val)).2 (Fin.natAdd (n+1) i) at hh
    simpa only [canonical_old,eta,replace] using hh
  affine p q ht hl := by
    have hOld : p.val.2 = q.val.2 := by
      funext i
      have hh := congrFun hl (Fin.natAdd (n+1) i)
      change (canonical (eta R p.val)).2 (Fin.natAdd (n+1) i) =
        (canonical (eta R q.val)).2 (Fin.natAdd (n+1) i) at hh
      simpa only [canonical_old,eta,replace] using hh
    have hBase : dropHead id p.val = dropHead id q.val := Prod.ext (funext ht) hOld
    have hc : centre R p.val = centre R q.val := congrArg (fun b => Barycentre.mean (R.fibre b)) hBase
    change (vfAt p.val 0-centre R p.val)-(vfAt q.val 0-centre R q.val) = _
    rw [hc]
    abel
  inverse_rv p q he := by
    obtain ⟨hv,hl⟩ := (sameRV_iff _ _).mp he
    have hOld : p.val.2 = q.val.2 := by
      funext i
      have hh := congrFun hl (Fin.natAdd (n+1) i)
      change (canonical (eta R p.val)).2 (Fin.natAdd (n+1) i) =
        (canonical (eta R q.val)).2 (Fin.natAdd (n+1) i) at hh
      simpa only [canonical_old,eta,replace] using hh
    apply (sameRV_iff _ _).mpr
    refine ⟨?_,hOld⟩
    intro i
    cases i using Fin.cases with
    | zero => exact (hTag p.val p.property).symm.trans ((congrFun hOld k).trans (hTag q.val q.property))
    | succ i => exact hv i.succ

@[simp] theorem step_apply (R : VerticalRootFamily A) (h00 : M ⊨ Axioms.ACVF00) (N : ℕ)
    (hN : ∀ p, (R.fibre p).card ≤ N) (k : Fin m) (hTag : Tagged (carrier A) 0 k) (p : A) :
    ((step R h00 N hN k hTag).toMap p).val = canonical (eta R p.val) := rfl

theorem centre_sameRV (R : VerticalRootFamily A) (h00 : M ⊨ Axioms.ACVF00)
    (k : Fin m) (hTag : Tagged (carrier A) 0 k) (p : A)
    (hne : (R.fibre (dropHead id p.val)).Nonempty) : rv (centre R p.val) = rv (vfAt p.val 0) := by
  apply mean_sameRV h00 _ hne (vfAt p.val 0)
  intro y hy
  have ht := hTag _ (R.subset ((R.mem_fibre _ _).mp hy))
  exact ht.symm.trans (hTag p.val p.property)

theorem etaImage_headSaturated (R : VerticalRootFamily A) (h00 : M ⊨ Axioms.ACVF00) (N : ℕ)
    (hN : ∀ p, (R.fibre p).card ≤ N) (k : Fin m) (hTag : Tagged (carrier A) 0 k)
    (hA : HeadSaturated (carrier A)) : HeadSaturated (carrier (etaImage R h00 N hN)) := by
  rintro p ⟨a,rfl⟩ x hx
  change rv x = rv (vfAt (eta R a.val) 0) at hx
  let z := replace 0 a.val (x+centre R a.val)
  have hzRV : rv (x+centre R a.val) = rv (vfAt a.val 0) := by
    by_cases hn : (R.fibre (dropHead id a.val)).Nonempty
    · have hc := centre_sameRV R h00 k hTag a hn
      exact rv_add_back (vfAt a.val 0) (centre R a.val) (centre R a.val) x hc hc hx
    · have he : R.fibre (dropHead id a.val) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      have hc : centre R a.val = 0 := by simp [centre,he,Barycentre.mean]
      simpa only [hc,add_zero,eta,replace,vfAt,Function.update_self,sub_zero] using hx
  have hz : z ∈ carrier A := hA a.val a.property _ hzRV
  refine ⟨⟨z,hz⟩,?_⟩
  change eta R z = replace 0 (eta R a.val) x
  have hBase : dropHead id z = dropHead id a.val := dropHead_replace_zero _ _ _
  have hc : centre R z = centre R a.val := congrArg (fun b => Barycentre.mean (R.fibre b)) hBase
  apply Prod.ext
  · funext i
    cases i using Fin.cases with
    | zero => change (x+centre R a.val)-centre R z = x; rw [hc,add_sub_cancel_right]
    | succ i => simp [eta,z,replace,vfAt,Fin.succ_ne_zero]
  · rfl

end IntegrationInACVF.Section4.VerticalMeanStep
