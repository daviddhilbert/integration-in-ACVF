import Integration7.RVLabelConstraintHeadProductImages

/-! For an independent trailing RV factor, the checked shared-label
head construction is an actual bijection onto the full product. The
original labels of the unary source are recovered from its prepared head. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Milestone0.sortEval SpecialTransformations.Section4.realSpace
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {S : Set M} {a b d : ℕ}
variable {A : DefSet (M := M) S 1 a} {B : DefSet (M := M) S 1 b}
variable {T : SpecialBijection A B} {H : DefSet (M := M) S 1 (a+d)} {Q : DefSet (M := M) S 0 (a+d)}
namespace RVLabelConstraintSpecialPreparation

def independentCoefficientMap (L : RVLabelConstraintSpecialPreparation T H Q (Fin.castAdd d) P)
    (R : DefSet (M := M) S 0 d)
    (hQ : ∀ q : Point (M := M) 0 (a+d), q ∈ carrier Q ↔ (Fin.elim0,q.2 ∘ Fin.natAdd a) ∈ carrier R) :
    Map (headImage L.target) R := by
  let J : Map Q (PresentedSet.univ (pointSpace (M := M) 0 (a+d)) S) :=
    Map.inclusion (fun _ _ => Set.mem_univ _)
  exact mapIntoSubset (Map.comp (rvCoordinatePointMap (Fin.natAdd a : Fin d → Fin (a+d)) S)
    (Map.comp J L.headParameterMap)) R (fun p => (hQ _).mp (L.headParameterMap p).property)

def independentHeadProductMap (L : RVLabelConstraintSpecialPreparation T H Q (Fin.castAdd d) P)
    (R : DefSet (M := M) S 0 d)
    (hQ : ∀ q : Point (M := M) 0 (a+d), q ∈ carrier Q ↔ (Fin.elim0,q.2 ∘ Fin.natAdd a) ∈ carrier R) :
    Map (headImage L.target) (PresentedSet.prod R (headImage B)) :=
  Map.pair (L.independentCoefficientMap R hQ) L.headPreparedMap

theorem independent_head_product_map_bijective
    (L : RVLabelConstraintSpecialPreparation T H Q (Fin.castAdd d) P)
    (R : DefSet (M := M) S 0 d)
    (hQ : ∀ q : Point (M := M) 0 (a+d), q ∈ carrier Q ↔ (Fin.elim0,q.2 ∘ Fin.natAdd a) ∈ carrier R) :
    Function.Bijective (L.independentHeadProductMap R hQ) := by
  constructor
  · intro p q he
    have hB := congrArg (fun z : PresentedSet.prod R (headImage B) => z.val.2.2) he
    have hR := congrArg (fun z : PresentedSet.prod R (headImage B) => z.val.1.2) he
    apply L.head_product_map_injective
    apply Subtype.ext
    rw [head_product_map_value,head_product_map_value]
    apply Prod.ext
    · apply Prod.ext (Subsingleton.elim _ _)
      funext j
      cases j using Fin.addCases with
      | left j =>
        exact (congrFun (L.head_product_map_compatible p) j).symm.trans
          ((congrArg (fun r : Fin (1+b) → RV (M := M) => r (Fin.natAdd 1
            (suffixIndex (special_chain_rvArity_le T.chain) j))) hB).trans
              (congrFun (L.head_product_map_compatible q) j))
      | right j => exact congrFun hR j
    · exact Prod.ext (Subsingleton.elim _ _) hB
  · intro q
    let c := Fin.append ((q.val.2.2 ∘ Fin.natAdd 1) ∘ suffixIndex (special_chain_rvArity_le T.chain)) q.val.1.2
    have hc : (Fin.elim0,c) ∈ carrier Q := by
      apply (hQ _).mpr
      have he : c ∘ Fin.natAdd a = q.val.1.2 := funext (Fin.append_right _ _)
      rw [he]
      exact (congrArg (fun z : Point (M := M) 0 d => z ∈ carrier R)
        (show (Fin.elim0,q.val.1.2)=q.val.1 from Prod.ext (Subsingleton.elim _ _) rfl)).mpr q.property.1
    let qBig : PresentedSet.prod Q (headImage B) := ⟨((Fin.elim0,c),q.val.2),hc,q.property.2⟩
    have hCompatible : (qBig.val.2.2 ∘ Fin.natAdd 1) ∘ suffixIndex (special_chain_rvArity_le T.chain) =
        qBig.val.1.2 ∘ Fin.castAdd d := by
      funext j
      exact (Fin.append_left _ _ j).symm
    obtain ⟨p,hp⟩ := L.head_product_map_preimage qBig hCompatible
    refine ⟨p,Subtype.ext ?_⟩
    apply Prod.ext
    · apply Prod.ext (Subsingleton.elim _ _)
      funext j
      have hr := congrArg (fun z : PresentedSet.prod Q (headImage B) => z.val.1.2 (Fin.natAdd a j)) hp
      exact hr.trans (Fin.append_right _ _ j)
    · exact congrArg (fun z : PresentedSet.prod Q (headImage B) => z.val.2) hp
end RVLabelConstraintSpecialPreparation
end IntegrationInACVF.Section7
