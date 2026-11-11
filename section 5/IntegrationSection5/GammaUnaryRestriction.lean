import IntegrationSection5.GammaUnaryChain

/-! Restriction and real certification of actual Gamma unary chains. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {n m l : ℕ}
variable {A : Set (Point (M := M) n m)} {B : Set (Point (M := M) n l)}

def gammaRestrictionTarget (e : GammaIso G A B) (D : Set (Point (M := M) n m)) (hDA : D ⊆ A) :
    Set (Point (M := M) n l) := Set.range (fun a : D => (e.equiv ⟨a.val,hDA a.property⟩).val)

def gammaRestrictionIso (e : GammaIso G A B) (D : Set (Point (M := M) n m))
    (hDA : D ⊆ A) (hD : GammaSetDefinable G D) : GammaIso G D (gammaRestrictionTarget e D hDA) where
  equiv := Equiv.ofInjective (fun a : D => (e.equiv ⟨a.val,hDA a.property⟩).val) (by
    intro a b he
    have h := e.equiv.injective (Subtype.ext he)
    exact Subtype.ext (congrArg (fun a : A => a.val) h))
  graph := by
    apply GammaGraphDefinable.congr ((gammaLogicInput G).restrict_graph hD e.graph)
    intro p q
    constructor
    · rintro ⟨hp,a,ha,hq⟩
      have he : a = ⟨p,hDA hp⟩ := Subtype.ext ha
      refine ⟨⟨p,hp⟩,rfl,?_⟩
      change (e.equiv ⟨p,hDA hp⟩).val = q
      exact (congrArg (fun a : A => (e.equiv a).val) he).symm.trans hq
    · rintro ⟨a,ha,hq⟩
      exact ⟨ha ▸ a.property,⟨a.val,hDA a.property⟩,ha,hq⟩

theorem gammaRestrictionTarget_subset (e : GammaIso G A B) (D : Set (Point (M := M) n m))
    (hDA : D ⊆ A) : gammaRestrictionTarget e D hDA ⊆ B := by
  rintro q ⟨a,rfl⟩
  exact (e.equiv ⟨a.val,hDA a.property⟩).property

namespace GammaUnaryChain

def congrTarget {B' : Set (Point (M := M) n l)} (T : GammaUnaryChain G n A B)
    (hB : B = B') : GammaUnaryChain G n A B' := hB ▸ T

theorem congrTarget_val {B' : Set (Point (M := M) n l)} (T : GammaUnaryChain G n A B)
    (hB : B = B') (a : A) : ((T.congrTarget hB).toIso.equiv a).val = (T.toIso.equiv a).val := by
  subst B'
  rfl

theorem restrict_exists (T : GammaUnaryChain G n A B) (D : Set (Point (M := M) n m))
    (hDA : D ⊆ A) (hD : GammaSetDefinable G D) :
    ∃ C : Set (Point (M := M) n l), ∃ U : GammaUnaryChain G n D C,
      C ⊆ B ∧ ∀ a : D, (U.toIso.equiv a).val = (T.toIso.equiv ⟨a.val,hDA a.property⟩).val := by
  induction T with
  | nil A hA => exact ⟨D,.nil D hD,hDA,fun _ => rfl⟩
  | @cons m l k A B C i e hi tail ih =>
    let E := gammaRestrictionTarget e D hDA
    let er := gammaRestrictionIso e D hDA hD
    have hEB := gammaRestrictionTarget_subset e D hDA
    obtain ⟨F,U,hFC,hU⟩ := ih E hEB (er.target_definable (gammaLogicInput G))
    refine ⟨F,.cons i er (fun a j hj => hi ⟨a.val,hDA a.property⟩ j hj) U,hFC,?_⟩
    intro a
    exact hU (er.equiv a)

theorem restrict_exact (T : GammaUnaryChain G n A B) (D : Set (Point (M := M) n m))
    (hDA : D ⊆ A) (hD : GammaSetDefinable G D) :
    ∃ U : GammaUnaryChain G n D (gammaRestrictionTarget T.toIso D hDA),
      ∀ a : D, (U.toIso.equiv a).val = (T.toIso.equiv ⟨a.val,hDA a.property⟩).val := by
  obtain ⟨C,U,hCB,hU⟩ := T.restrict_exists D hDA hD
  have hC : C = gammaRestrictionTarget T.toIso D hDA := by
    ext q
    constructor
    · intro hq
      obtain ⟨a,ha⟩ := U.toIso.equiv.surjective ⟨q,hq⟩
      exact ⟨a,(hU a).symm.trans (congrArg (fun b : C => b.val) ha)⟩
    · rintro ⟨a,ha⟩
      exact (hU a).trans ha ▸ (U.toIso.equiv a).property
  exact ⟨U.congrTarget hC,fun a => (U.congrTarget_val hC a).trans (hU a)⟩

/-- Real maps over the original real base acquire their full Gamma graphs
from the checked interpretation bridge. -/
theorem ofReal {m l : ℕ} {A : DefSet (M := M) G.real n m} {B : DefSet (M := M) G.real n l}
    (T : UnaryChain G.real n A B) :
    ∃ U : GammaUnaryChain G n (carrier A) (carrier B),
      ∀ a : A, (U.toIso.equiv a).val = (T.toMap a).val := by
  induction T with
  | nil A => exact ⟨.nil (carrier A) ((gammaLogicInput G).real_set _ (setDefinable A)),fun _ => rfl⟩
  | @cons m l k A B C i f hf hi tail ih =>
    obtain ⟨U,hU⟩ := ih
    let e : GammaIso G (carrier A) (carrier B) :=
      { equiv := Equiv.ofBijective (fun a : A => f a) hf
        graph := (gammaLogicInput G).real_map_graph f }
    exact ⟨.cons i e hi U,fun a => hU (f a)⟩

end GammaUnaryChain
end IntegrationInACVF.Section5
