import IntegrationSection3ACVF.ThinFamilyConservation

/-! The one-component form of 3.22, with the actual hole counts. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open scoped BigOperators
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3ACVF.PuncturedGeometry
open IntegrationInACVF.Section3ACVF.ThinFamilyGeometry

namespace IntegrationInACVF.Section3ACVF.ThinBallHoleConservation

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem body_singleton (d : PuncturedBall M) : body {d} = d.body := by
  ext x
  simp only [body,Set.mem_ofPred_eq,Finset.mem_singleton,exists_eq_left]

theorem holes_eq (B : FullBaseAtomicity.Base (M := M))
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (d e : PuncturedBall M) (hd : IsThin d) (he : IsThin e)
    (f : M → M)
    (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn d.body f))
    (hbij : Set.BijOn f d.body e.body) (hoo : MaximalOpenClasses.OpenToOpen d.body f) :
    d.holes.card = e.holes.card := by
  classical
  have hdf : ∀ a ∈ ({d} : Finset (PuncturedBall M)), IsThin a := by simpa only [Finset.mem_singleton,forall_eq] using hd
  have hef : ∀ a ∈ ({e} : Finset (PuncturedBall M)), IsThin a := by simpa only [Finset.mem_singleton,forall_eq] using he
  have hdDis : (({d} : Finset (PuncturedBall M)) : Set (PuncturedBall M)).Pairwise
      (fun a b => Disjoint a.body b.body) := by simp
  have heDis : (({e} : Finset (PuncturedBall M)) : Set (PuncturedBall M)).Pairwise
      (fun a b => Disjoint a.body b.body) := by simp
  have hf' : FullBaseAtomicity.OverBase B
      {z : Fin 2 → M | z 0 ∈ body {d} ∧ z 1 = f (z 0)} := by rwa [body_singleton]
  have hb' : Set.BijOn f (body {d}) (body {e}) := by rwa [body_singleton,body_singleton]
  have ho' : MaximalOpenClasses.OpenToOpen (body {d}) f := by rwa [body_singleton]
  have hc := ThinFamilyConservation.lemma_3_22 B δ hδ {d} {e} hdf hef hdDis heDis f hf' hb' ho'
  have hs (a : PuncturedBall M) : (∑ b : ({a} : Finset (PuncturedBall M)), b.val.holes.card) = a.holes.card :=
    (Finset.sum_coe_sort {a} (fun b : PuncturedBall M => b.holes.card)).trans (Finset.sum_singleton _ _)
  exact (hs d).symm.trans (hc.2.trans (hs e))

end IntegrationInACVF.Section3ACVF.ThinBallHoleConservation
