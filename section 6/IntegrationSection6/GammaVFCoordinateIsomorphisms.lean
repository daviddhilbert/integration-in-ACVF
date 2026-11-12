import IntegrationSection6.GammaRealImages
import IntegrationSection6.MixedCoordinatePointMaps

/-! Actual Gamma isomorphisms for bijective reindexing of VF coordinates,
with every RV label unchanged. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Section4.vfSpace
  SpecialTransformations.Section4.rvSpace SpecialTransformations.Milestone0.sortEval
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n r a : ℕ}

def vfCoordinateMap (S : Set M) (e : Fin r ≃ Fin n) (a : ℕ) :
    Map (PresentedSet.univ (pointSpace (M := M) n a) S)
      (PresentedSet.univ (pointSpace (M := M) r a) S) := mixedCoordinatePointMap e id S

theorem vfCoordinateMap_value (S : Set M) (e : Fin r ≃ Fin n)
    (q : PresentedSet.univ (pointSpace (M := M) n a) S) :
    (vfCoordinateMap S e a q).val = (q.val.1 ∘ e,q.val.2) := rfl

theorem vfCoordinateMap_injective (S : Set M) (e : Fin r ≃ Fin n) :
    Function.Injective (vfCoordinateMap S e a) := by
  intro x y he
  have h : (x.val.1 ∘ e,x.val.2) = (y.val.1 ∘ e,y.val.2) := congrArg Subtype.val he
  have hf : x.val.1 ∘ e = y.val.1 ∘ e := congrArg Prod.fst h
  have hr : x.val.2 = y.val.2 := congrArg (fun z : Point (M := M) r a => z.2) h
  apply Subtype.ext
  change (x.val.1,x.val.2) = (y.val.1,y.val.2)
  apply Prod.ext ?_ hr
  funext j
  obtain ⟨i,rfl⟩ := e.surjective j
  exact congrFun hf i

theorem vfCoordinateMap_image (S : Set M) (e : Fin r ≃ Fin n)
    (A : Set (Point (M := M) n a)) (q : Point (M := M) r a) :
    (∃ p, p ∈ A ∧ (vfCoordinateMap S e a ⟨p,Set.mem_univ _⟩).val = q) ↔
      (q.1 ∘ e.symm,q.2) ∈ A := by
  constructor
  · rintro ⟨p,hp,he⟩
    have h : (q.1 ∘ e.symm,q.2) = p := by
      have he' : (p.1 ∘ e,p.2) = q := he
      apply Prod.ext
      · funext j
        have hi := congrFun (congrArg Prod.fst he') (e.symm j)
        simpa only [Function.comp_apply,Equiv.apply_symm_apply] using hi.symm
      · exact (congrArg Prod.snd he').symm
    exact h.symm ▸ hp
  · intro hq
    refine ⟨(q.1 ∘ e.symm,q.2),hq,?_⟩
    apply Prod.ext
    · funext j
      exact congrArg q.1 (e.symm_apply_apply j)
    · rfl

def gammaVFCoordinateIso (A : Set (Point (M := M) n a)) (hA : GammaSetDefinable B A)
    (e : Fin r ≃ Fin n) : GammaIso B A {q : Point (M := M) r a | (q.1 ∘ e.symm,q.2) ∈ A} := by
  let f := gammaIso_realImage A hA (vfCoordinateMap B.real e a) (vfCoordinateMap_injective B.real e)
  apply f.congr rfl
  ext q
  constructor
  · rintro ⟨x,hx⟩
    exact (vfCoordinateMap_image B.real e A q).mp ⟨x.val,x.property,hx⟩
  · intro hq
    obtain ⟨x,hx,he⟩ := (vfCoordinateMap_image B.real e A q).mpr hq
    exact ⟨⟨x,hx⟩,he⟩

end IntegrationInACVF.Section6
