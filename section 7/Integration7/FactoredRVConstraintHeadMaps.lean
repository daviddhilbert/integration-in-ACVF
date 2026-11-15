import Integration7.RVLabelConstraintHeadProductImages
import Section4.MapProduct

/-! Extra functional RV labels can be retained through a unary head
preparation. A genuine pure-RV factorization of its constraint supplies
an actual product head bijection, without discarding those labels. -/
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
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {S : Set M} {a b l d : ℕ}
variable {A : DefSet (M := M) S 1 a} {B : DefSet (M := M) S 1 b}
variable {T : SpecialBijection A B} {H : DefSet (M := M) S 1 l} {Q : DefSet (M := M) S 0 l}
variable {ρ : Fin a → Fin l}
namespace RVLabelConstraintSpecialPreparation

def factoredCoefficientMap (L : RVLabelConstraintSpecialPreparation T H Q ρ P)
    (R : DefSet (M := M) S 0 d)
    (Φ : Map Q (PresentedSet.prod (PresentedSet.univ (pointSpace (M := M) 0 a) S) R)) :
    Map (headImage L.target) R := by
  let snd : Map (PresentedSet.prod (PresentedSet.univ (pointSpace (M := M) 0 a) S) R) R :=
    @SpecialTransformations.DefinableGeometry.Map.prodSnd LRV M (@CanonicalStructure.normalize M sM) _ _ S _ _
  exact Map.comp snd (Map.comp Φ L.headParameterMap)

def factoredHeadProductMap (L : RVLabelConstraintSpecialPreparation T H Q ρ P)
    (R : DefSet (M := M) S 0 d)
    (Φ : Map Q (PresentedSet.prod (PresentedSet.univ (pointSpace (M := M) 0 a) S) R)) :
    Map (headImage L.target) (PresentedSet.prod R (headImage B)) :=
  Map.pair (L.factoredCoefficientMap R Φ) L.headPreparedMap

theorem factored_head_product_map_bijective
    (L : RVLabelConstraintSpecialPreparation T H Q ρ P)
    (R : DefSet (M := M) S 0 d)
    (Φ : Map Q (PresentedSet.prod (PresentedSet.univ (pointSpace (M := M) 0 a) S) R))
    (hΦ : Function.Bijective Φ) (hOld : ∀ z : Q, (Φ z).val.1.2=z.val.2 ∘ ρ) :
    Function.Bijective (L.factoredHeadProductMap R Φ) := by
  constructor
  · intro p q he
    have hB := congrArg (fun z : PresentedSet.prod R (headImage B) => z.val.2.2) he
    have hR := congrArg (fun z : PresentedSet.prod R (headImage B) => z.val.1.2) he
    have hF : Φ (L.headParameterMap p)=Φ (L.headParameterMap q) := by
      apply Subtype.ext
      apply Prod.ext
      · apply Prod.ext (Subsingleton.elim _ _)
        rw [hOld,hOld]
        exact (L.head_product_map_compatible p).symm.trans
          ((congrArg (fun r : Fin (1+b) → RV (M := M) => (r ∘ Fin.natAdd 1) ∘
            suffixIndex (special_chain_rvArity_le T.chain)) hB).trans (L.head_product_map_compatible q))
      · exact Prod.ext (Subsingleton.elim _ _) hR
    have hQ := congrArg (fun z : Q => z.val.2) (hΦ.1 hF)
    apply L.head_product_map_injective
    apply Subtype.ext
    exact Prod.ext (Prod.ext (Subsingleton.elim _ _) hQ) (Prod.ext (Subsingleton.elim _ _) hB)
  · intro q
    let old : PresentedSet.univ (pointSpace (M := M) 0 a) S :=
      ⟨(Fin.elim0,(q.val.2.2 ∘ Fin.natAdd 1) ∘ suffixIndex (special_chain_rvArity_le T.chain)),Set.mem_univ _⟩
    let zTarget : PresentedSet.prod (PresentedSet.univ (pointSpace (M := M) 0 a) S) R :=
      ⟨(old.val,q.val.1),old.property,q.property.1⟩
    obtain ⟨z,hz⟩ := hΦ.2 zTarget
    let big : PresentedSet.prod Q (headImage B) := ⟨(z.val,q.val.2),z.property,q.property.2⟩
    have hCompatible : (big.val.2.2 ∘ Fin.natAdd 1) ∘ suffixIndex (special_chain_rvArity_le T.chain) =
        big.val.1.2 ∘ ρ := by
      exact (congrArg (fun w : PresentedSet.prod (PresentedSet.univ (pointSpace (M := M) 0 a) S) R => w.val.1.2) hz).symm.trans (hOld z)
    obtain ⟨p,hp⟩ := L.head_product_map_preimage big hCompatible
    have hpQ : L.headParameterMap p=z := Subtype.ext (Prod.ext (Subsingleton.elim _ _)
      (congrArg (fun w : PresentedSet.prod Q (headImage B) => w.val.1.2) hp))
    refine ⟨p,Subtype.ext ?_⟩
    apply Prod.ext
    · change (Φ (L.headParameterMap p)).val.2=q.val.1
      rw [hpQ,hz]
    · exact congrArg (fun w : PresentedSet.prod Q (headImage B) => w.val.2) hp
end RVLabelConstraintSpecialPreparation
end IntegrationInACVF.Section7
