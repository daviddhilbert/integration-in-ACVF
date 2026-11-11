import IntegrationSection5.RVContractionMaps
import IntegrationSection5.GammaGraphOperations

/-! The induced RV map keeps its complete invariant graph over the original
Gamma base, even when its real presentation uses internal representatives. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3

namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : GammaParameters.Base (M := M)} {S : Set M} {n m l : ℕ}
variable {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l}

def mixedKeyPoint (p : Point (M := M) n m) : Point (M := M) 0 (n+m) :=
  (Fin.elim0,Fin.append (key p).1 (key p).2)

def mixedKeyPointMap (S : Set M) (n m : ℕ) :
    Map (PresentedSet.univ (pointSpace (M := M) n m) S)
      (PresentedSet.univ (pointSpace 0 (n+m)) S) :=
  Map.comp (flattenKeyMap (PresentedSet.univ (keySpace n m) S))
    (keyMap (PresentedSet.univ (pointSpace n m) S))

theorem gamma_key_relation (f : Map A B) (hf : GammaGraphDefinable P (pointMapGraph f)) :
    GammaGraphDefinable P (fun p q => ∃ a : A, mixedKeyPoint a.val = p ∧ mixedKeyPoint (f a).val = q) := by
  let L := gammaLogicInput P
  have h := L.comp_graph (L.swap_graph (L.real_map_graph (mixedKeyPointMap P.real n m)))
    (L.comp_graph hf (L.real_map_graph (mixedKeyPointMap P.real n l)))
  apply GammaGraphDefinable.congr h
  intro p q
  constructor
  · rintro ⟨z,⟨a,ha,hp⟩,w,⟨c,hc,hw⟩,⟨b,hb,hq⟩⟩
    have hsource : a.val = c.val := ha.trans hc.symm
    have htarget : b.val = (f c).val := hb.trans hw.symm
    change mixedKeyPoint a.val = p at hp
    change mixedKeyPoint b.val = q at hq
    rw [hsource] at hp
    rw [htarget] at hq
    exact ⟨c,hp,hq⟩
  · rintro ⟨a,hp,hq⟩
    exact ⟨a.val,⟨⟨a.val,Set.mem_univ _⟩,rfl,hp⟩,(f a).val,⟨a,rfl,rfl⟩,
      ⟨(f a).val,Set.mem_univ _⟩,rfl,hq⟩

theorem gamma_rvContractionMap_graph (f : Map A B) (hc : Contractible f)
    (hf : GammaGraphDefinable P (pointMapGraph f)) :
    GammaGraphDefinable P
      (fun (p : Point (M := M) 0 (n+m)) (q : Point (M := M) 0 (n+l)) =>
        ∃ a : rvObjectDomain (pullbackObject A), a.val = p.2 ∧ (rvContractionMap f hc a).val = q.2) := by
  apply GammaGraphDefinable.congr (gamma_key_relation f hf)
  intro p q
  constructor
  · rintro ⟨a,hp,hq⟩
    refine ⟨Map.toImage (rawKeyMap A) a,congrArg Prod.snd hp,?_⟩
    rw [rvContractionMap_spec]
    exact congrArg Prod.snd hq
  · rintro ⟨u,hp,hq⟩
    obtain ⟨a,rfl⟩ := rawKeyImage_surjective A u
    rw [rvContractionMap_spec] at hq
    exact ⟨a,Prod.ext (Subsingleton.elim _ _) hp,Prod.ext (Subsingleton.elim _ _) hq⟩

end IntegrationInACVF.Section5
