import IntegrationSection5.GammaMapPresentation
import Section5.GammaLift
import IntegrationSection5.UnaryFactorizations

/-! Finite chains of actual original-Gamma bijections, together with a
realization theorem producing the existing definable UnaryChain over one
common internal real presentation. -/
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
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def gammaSetIdentityIso (G : GammaParameters.Base (M := M)) {n m : ℕ}
    (A : Set (Point (M := M) n m)) (hA : GammaSetDefinable G A) : GammaIso G A A where
  equiv := Equiv.refl A
  graph := by
    let U := PresentedSet.univ (pointSpace (M := M) n m) G.real
    apply GammaGraphDefinable.congr ((gammaLogicInput G).restrict_graph hA
      ((gammaLogicInput G).real_map_graph (Map.id U)))
    intro p q
    constructor
    · rintro ⟨hp,a,ha,hq⟩
      exact ⟨⟨p,hp⟩,rfl,ha.symm.trans hq⟩
    · rintro ⟨a,ha,hq⟩
      exact ⟨ha ▸ a.property,⟨a.val,Set.mem_univ _⟩,ha,hq⟩

/-- Full original-Gamma certificates for every actual factor, including the
last object's domain. -/
def GammaUnaryChainDefinable (G : GammaParameters.Base (M := M)) {S : Set M} {n : ℕ}
    {m l : ℕ} {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l} :
    UnaryChain S n A B → Prop
  | .nil A => GammaSetDefinable G (carrier A)
  | .cons _ f _ _ tail => GammaGraphDefinable G (pointMapGraph f) ∧ GammaUnaryChainDefinable G tail

inductive GammaUnaryChain (G : GammaParameters.Base (M := M)) (n : ℕ) :
    {m l : ℕ} → Set (Point (M := M) n m) → Set (Point (M := M) n l) → Type where
  | nil {m : ℕ} (A : Set (Point (M := M) n m)) (hA : GammaSetDefinable G A) : GammaUnaryChain G n A A
  | cons {m l k : ℕ} {A : Set (Point (M := M) n m)} {B : Set (Point (M := M) n l)}
      {C : Set (Point (M := M) n k)} (i : Fin n) (e : GammaIso G A B)
      (unary : ∀ a : A, ∀ j : Fin n, j ≠ i → (e.equiv a).val.1 j = a.val.1 j)
      (tail : GammaUnaryChain G n B C) : GammaUnaryChain G n A C

namespace GammaUnaryChain
variable {G : GammaParameters.Base (M := M)} {n m l k : ℕ}
variable {A : Set (Point (M := M) n m)} {B : Set (Point (M := M) n l)}
variable {C : Set (Point (M := M) n k)}

def toIso {m l : ℕ} {A : Set (Point (M := M) n m)} {B : Set (Point (M := M) n l)} :
    GammaUnaryChain G n A B → GammaIso G A B
  | .nil A hA => gammaSetIdentityIso G A hA
  | .cons _ e _ tail => e.trans (gammaLogicInput G) tail.toIso

def append {m l k : ℕ} {A : Set (Point (M := M) n m)}
    {B : Set (Point (M := M) n l)} {C : Set (Point (M := M) n k)} :
    GammaUnaryChain G n A B → GammaUnaryChain G n B C → GammaUnaryChain G n A C
  | .nil _ _,u => u
  | .cons i e hi tail,u => .cons i e hi (tail.append u)

theorem append_apply (t : GammaUnaryChain G n A B) (u : GammaUnaryChain G n B C) (a : A) :
    (t.append u).toIso.equiv a = u.toIso.equiv (t.toIso.equiv a) := by
  induction t with
  | nil A hA => rfl
  | cons i e hi tail ih => exact ih u (e.equiv a)

/-- Every Gamma-certified chain is realized by actual definable maps in the
existing UnaryChain, over a common real base containing any requested S. -/
theorem realize (T : GammaUnaryChain G n A B) (S : Set M) :
    ∃ R : Set M, S ⊆ R ∧
      ∃ hA : SetDefinable (pointSpace n m) R A,
      ∃ hB : SetDefinable (pointSpace n l) R B,
      ∃ t : UnaryChain R n (PresentedSet.mk A hA) (PresentedSet.mk B hB),
        GammaUnaryChainDefinable G t ∧
        ∀ a : A, (t.toMap a).val = (T.toIso.equiv a).val := by
  induction T generalizing S with
  | @nil m A hA =>
    obtain ⟨R,hGR,hAr,_,_⟩ := common_gamma_presentation A A (Equiv.refl A) hA hA
      (gammaSetIdentityIso G A hA).graph
    let R' := S ∪ R
    have hRR' : R ⊆ R' := Set.subset_union_right
    have hA' := SetDefinable.mono (pointSpace n m) hAr hRR'
    exact ⟨R',Set.subset_union_left,hA',hA',.nil _,hA,fun _ => rfl⟩
  | @cons m l k A B C i e hi tail ih =>
    have hA := (e.symm (gammaLogicInput G)).target_definable (gammaLogicInput G)
    have hB := e.target_definable (gammaLogicInput G)
    obtain ⟨R₁,_,hAr,_,her⟩ := common_gamma_presentation A B e.equiv hA hB e.graph
    obtain ⟨R,hSR,hBr,hCr,t,htG,ht⟩ := ih (S ∪ R₁)
    have hR₁R : R₁ ⊆ R := Set.Subset.trans Set.subset_union_right hSR
    have hAr' := SetDefinable.mono (pointSpace n m) hAr hR₁R
    have her' := RelationDefinable.mono (pointSpace n m) (pointSpace n l) her hR₁R
    let f : Map (M := M) (sM := sM)
        (@PresentedSet.mk M sM (pointSpace n m) R A hAr')
        (@PresentedSet.mk M sM (pointSpace n l) R B hBr) :=
      @Map.mk M sM (pointSpace n m) (pointSpace n l) R
        (@PresentedSet.mk M sM (pointSpace n m) R A hAr')
        (@PresentedSet.mk M sM (pointSpace n l) R B hBr) (fun a => e.equiv a) her'
    refine ⟨R,Set.Subset.trans Set.subset_union_left hSR,hAr',hCr,
      .cons i f e.equiv.bijective hi t,⟨e.graph,htG⟩,?_⟩
    intro a
    exact ht (e.equiv a)

end GammaUnaryChain
end IntegrationInACVF.Section5
