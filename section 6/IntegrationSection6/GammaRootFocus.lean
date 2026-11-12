import IntegrationSection6.RootFocus
import IntegrationSection6.GlobalRootSelection
import Section5.GammaInvariantLogic

/-! The constructed focus retains its original Gamma graph certificate.
Use the real-base selector on its whole validity domain, then restrict its
full graph to the original Gamma-definable source. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section6

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n m : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

theorem rootFocus_gamma (hBS : B.real ⊆ S)
    (A : DefSet (M := M) S n m) (R : Set (Fin n → M)) (j : Fin n) (k : Fin m)
    (hR : @Set.Definable M B.real LRV N (Fin n) R)
    (hcover : ∀ p ∈ carrier A, (fun i => (rv (p.1 i)).val) ∈ @rootDomain M N n R j)
    (hA : IsRVPullback (carrier A)) (htag : Tagged (carrier A) j k)
    (hADef : GammaSetDefinable B (carrier A)) :
    GammaFocusDefinable B (rootFocus A R j k hcover (@Set.Definable.mono M B.real LRV N (Fin n) S R hR hBS) hA htag) := by
  let D := rootSelectionDomain B.real m R hR j
  have hD : ∀ p ∈ carrier D,
      (fun i => (rv (p.1 i)).val) ∈ @rootDomain M N n R j := fun _ hp => hp
  let F := rootSelectionMap D R j hD hR
  let G := Map.comp (rootVFCoordinateMap B.real j) F
  let K := rootFocus A R j k hcover (@Set.Definable.mono M B.real LRV N (Fin n) S R hR hBS) hA htag
  have hagree (a : A) :
      (G ⟨a.val,hcover a.val a.property⟩).val 0 = K.center a.val := by
    let d : D := ⟨a.val,hcover a.val a.property⟩
    let b := (F d).val
    let c := (rootSelectionMap A R j hcover (@Set.Definable.mono M B.real LRV N (Fin n) S R hR hBS) a).val
    have hb := rootSelectionMap_spec D R j hD hR d
    have hc := rootSelectionMap_spec A R j hcover (@Set.Definable.mono M B.real LRV N (Fin n) S R hR hBS) a
    have hcd : rootSelectorRelation D R j a.val c :=
      ⟨d.property,hc.2⟩
    have he := rootSelector_unique D R j hD a.val b c hb hcd
    rw [rootFocus_center_apply]
    exact congrFun he j
  refine ⟨hADef,?_⟩
  let L := gammaLogicInput B
  have hr := L.restrict_graph hADef (L.real_scalar_graph G)
  apply GammaGraphDefinable.congr hr
  intro p z
  constructor
  · rintro ⟨hp,d,hd,hz⟩
    subst p
    refine ⟨⟨hp,hp⟩,?_⟩
    exact hz.symm.trans (hagree ⟨d.val,hp⟩)
  · rintro ⟨hp,hz⟩
    let a : A := ⟨p,hp.1⟩
    let d : D := ⟨p,hcover p hp.1⟩
    exact ⟨hp.1,d,rfl,(hagree a).trans hz.symm⟩

end IntegrationInACVF.Section6
