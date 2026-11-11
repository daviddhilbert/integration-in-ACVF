import IntegrationSection4.GammaRVMapOperations
import Section5.GammaLiftRelation

noncomputable section
set_option backward.isDefEq.respectTransparency false

set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5

namespace IntegrationInACVF.Section4.GammaRVMap

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {n m d : ℕ} {A : Set (Point (M := M) n m)}

def selectLabelsMap (S : Set M) (n : ℕ) {u v : ℕ} (ρ : Fin v → Fin u) :
    Map (PresentedSet.univ (pointSpace (M := M) n u) S)
      (PresentedSet.univ (pointSpace n v) S) :=
  Map.ofCodes _ (fun p => (p.1,p.2 ∘ ρ))
    (fun z => Sum.elim (z ∘ Sum.inl) (fun i => z (.inr (ρ i))))
    (by intro i; cases i with
        | inl i => exact rawProj S (.inl i : Fin n ⊕ Fin u)
        | inr i => exact rawProj S (.inr (ρ i) : Fin n ⊕ Fin u))
    (by intro c; exact ⟨c.property.1,fun i => c.property.2 (ρ i)⟩)
    (by intro c; refine Prod.ext ?_ ?_
        · funext i; apply Subtype.ext; rfl
        · funext i; apply Subtype.ext; rfl)

def attachment (P : GammaRVMap G A d) (a : A) : Point (M := M) n (m+d) :=
  (a.val.1,Fin.append a.val.2 (P.toFun a))

theorem attachment_graph (P : GammaRVMap G A d) :
    GammaGraphDefinable G (fun (p : Point (M := M) n m) (q : Point (M := M) n (m+d)) =>
      ∃ a : A, a.val = p ∧ attachment P a = q) := by
  let hΓ := gammaLogicInput G
  let drop := selectLabelsMap G.real n (Fin.castAdd d : Fin m → Fin (m+d))
  let tail := Map.comp (rvCoordinatePointMap (Fin.natAdd m : Fin d → Fin (m+d)) G.real)
    (pointLabels G.real n (m+d))
  have hDrop := hΓ.swap_graph (hΓ.real_map_graph drop)
  have hTail := hΓ.comp_graph P.graph (hΓ.swap_graph (hΓ.real_map_graph tail))
  have h := GammaGraphOperations.inter G hDrop hTail
  apply GammaGraphDefinable.congr h
  intro p q
  constructor
  · rintro ⟨⟨b,hb,he⟩,s,⟨a,ha,hPa⟩,c,hc,hs⟩
    have hcb : c = b := Subtype.ext (hc.trans hb.symm)
    subst c
    refine ⟨a,ha,?_⟩
    apply Prod.ext
    · have hh := congrArg Prod.fst (he.trans ha.symm)
      exact hh.symm.trans (congrArg Prod.fst hb)
    · funext i
      cases i using Fin.addCases with
      | left i =>
        have hh := congrFun (congrArg Prod.snd (he.trans ha.symm)) i
        change b.val.2 (Fin.castAdd d i) = a.val.2 i at hh
        change Fin.append a.val.2 (P.toFun a) (Fin.castAdd d i) = q.2 (Fin.castAdd d i)
        rw [Fin.append_left]
        exact hh.symm.trans (congrArg (fun p : Point (M := M) n (m+d) => p.2 (Fin.castAdd d i)) hb)
      | right i =>
        have hh := congrFun (congrArg Prod.snd hs) i
        have htail : (tail b).val.2 i = b.val.2 (Fin.natAdd m i) := by
          change (pointLabels G.real n (m+d) b).val.2 (Fin.natAdd m i) = _
          rw [pointLabels_snd]
        rw [htail] at hh
        change Fin.append a.val.2 (P.toFun a) (Fin.natAdd m i) = q.2 (Fin.natAdd m i)
        rw [Fin.append_right]
        exact (congrFun hPa i).trans (hh.symm.trans (congrArg (fun p : Point (M := M) n (m+d) => p.2 (Fin.natAdd m i)) hb))
  · rintro ⟨a,rfl,rfl⟩
    let b : PresentedSet.univ (pointSpace (M := M) n (m+d)) G.real := ⟨attachment P a,Set.mem_univ _⟩
    have hDrop : (drop b).val = a.val := by
      apply Prod.ext
      · rfl
      · funext i
        exact Fin.append_left _ _ i
    have hTail : (tail b).val = (Fin.elim0,P.toFun a) := by
      apply Prod.ext (Subsingleton.elim _ _)
      funext i
      change (pointLabels G.real n (m+d) b).val.2 (Fin.natAdd m i) = P.toFun a i
      rw [pointLabels_snd]
      exact Fin.append_right _ _ i
    exact ⟨⟨b,rfl,hDrop⟩,(Fin.elim0,P.toFun a),⟨a,rfl,rfl⟩,b,rfl,hTail⟩

end IntegrationInACVF.Section4.GammaRVMap
