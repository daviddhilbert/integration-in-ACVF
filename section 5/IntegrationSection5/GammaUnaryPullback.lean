import IntegrationSection5.GammaUnaryRestriction

/-! Definable preimages and actual unary-chain restrictions to target pieces. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {n m l : ℕ}
variable {A : Set (Point (M := M) n m)} {B : Set (Point (M := M) n l)}

def gammaIsoPreimage (e : GammaIso G A B) (E : Set (Point (M := M) n l)) :
    Set (Point (M := M) n m) := {p | ∃ a : A, a.val = p ∧ (e.equiv a).val ∈ E}

theorem gammaIsoPreimage_definable (e : GammaIso G A B) (E : Set (Point (M := M) n l))
    (hE : GammaSetDefinable G E) : GammaSetDefinable G (gammaIsoPreimage e E) := by
  have h := (gammaLogicInput G).image_graph ((gammaLogicInput G).restrict_graph hE
    ((gammaLogicInput G).swap_graph e.graph))
  convert h using 1
  ext p
  constructor
  · rintro ⟨a,ha,hE⟩
    exact ⟨(e.equiv a).val,hE,a,ha,rfl⟩
  · rintro ⟨q,hq,a,ha,he⟩
    exact ⟨a,ha,he.symm ▸ hq⟩

theorem gammaIsoPreimage_subset (e : GammaIso G A B) (E : Set (Point (M := M) n l)) :
    gammaIsoPreimage e E ⊆ A := by
  rintro p ⟨a,ha,_⟩
  exact ha ▸ a.property

theorem mem_gammaIsoPreimage (e : GammaIso G A B) (E : Set (Point (M := M) n l)) (a : A) :
    a.val ∈ gammaIsoPreimage e E ↔ (e.equiv a).val ∈ E := by
  constructor
  · rintro ⟨b,hb,hE⟩
    exact (Subtype.ext hb : b = a) ▸ hE
  · intro hE
    exact ⟨a,rfl,hE⟩

theorem GammaUnaryChain.pullback (T : GammaUnaryChain G n A B) (E : Set (Point (M := M) n l))
    (hEB : E ⊆ B) (hE : GammaSetDefinable G E) :
    ∃ U : GammaUnaryChain G n (gammaIsoPreimage T.toIso E) E,
      ∀ a : gammaIsoPreimage T.toIso E,
        (U.toIso.equiv a).val = (T.toIso.equiv ⟨a.val,gammaIsoPreimage_subset T.toIso E a.property⟩).val := by
  let D := gammaIsoPreimage T.toIso E
  let hDA := gammaIsoPreimage_subset T.toIso E
  obtain ⟨C,U,_,hU⟩ := T.restrict_exists D hDA (gammaIsoPreimage_definable T.toIso E hE)
  have hC : C = E := by
    ext q
    constructor
    · intro hq
      obtain ⟨a,ha⟩ := U.toIso.equiv.surjective ⟨q,hq⟩
      have hqE := (mem_gammaIsoPreimage T.toIso E ⟨a.val,hDA a.property⟩).mp a.property
      have he : (T.toIso.equiv ⟨a.val,hDA a.property⟩).val = q :=
        (hU a).symm.trans (congrArg (fun b : C => b.val) ha)
      rw [← he]
      exact hqE
    · intro hq
      obtain ⟨a,ha⟩ := T.toIso.equiv.surjective ⟨q,hEB hq⟩
      have haD : a.val ∈ D := (mem_gammaIsoPreimage T.toIso E a).mpr
        ((congrArg (fun b : B => b.val) ha).symm ▸ hq)
      let aD : D := ⟨a.val,haD⟩
      have he : (U.toIso.equiv aD).val = q := (hU aD).trans (congrArg (fun b : B => b.val) ha)
      exact he ▸ (U.toIso.equiv aD).property
  exact ⟨U.congrTarget hC,fun a => (U.congrTarget_val hC a).trans (hU a)⟩

end IntegrationInACVF.Section5
