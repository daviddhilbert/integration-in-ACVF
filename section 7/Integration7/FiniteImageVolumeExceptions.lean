import Integration7.VolumeAlmostEverywhereImages
import Section4.RVFinitaryImages
import Section4.EarlierRVInputs

/-! Move an exceptional locus to a definable RV image. All points above
a label outside that image satisfy the original assertion. This permits
exception formulas on coordinate-and-density labels rather than raw labels. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {a b n : ℕ}

theorem rvMap_image_dimension_le
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {A : DefSet (rawRVSpace (M := M) a) (C.base : Set M)}
    {B : DefSet (rawRVSpace (M := M) b) (C.base : Set M)} (F : Map A B) :
    rvDim F.image ≤ rvDim A := by
  let G : RVFinitaryFunction A b := {
    values := fun x => {y | F.graph x y}
    definable := F.graph_definable
    finite := fun x => F.graph_values_finite x.val }
  have he : G.image = F.image := by
    apply DefSet.eq_of_carrier_eq
    ext y
    constructor
    · rintro ⟨x,u,hu,huy⟩
      exact ⟨u,huy⟩
    · rintro ⟨u,hu⟩
      exact ⟨u,u,rfl,hu⟩
  have h := G.dimension_image_le hc
    (rvExchangeInput_of_earlier C.uncountable.le C.saturated C.model00) C.saturated C.small
  rwa [he] at h

theorem RVAlmostEverywhere.pushforward_all
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {A : DefSet (rawRVSpace (M := M) a) (C.base : Set M)}
    {B : DefSet (rawRVSpace (M := M) b) (C.base : Set M)}
    (F : Map A B) {P : A → Prop} (hP : RVAlmostEverywhere A n P) :
    RVAlmostEverywhere B n (fun b => ∀ a, F a = b → P a) := by
  obtain ⟨D,hDA,hd,hP⟩ := hP
  let g := F.restrict hDA
  refine ⟨g.image,?_,(rvMap_image_dimension_le hc C g).trans_lt hd,?_⟩
  · rintro y ⟨x,rfl⟩
    exact (g x).property
  · intro b hb a hab
    apply hP a
    intro ha
    exact hb ⟨⟨a.val,ha⟩,congrArg (fun b : B => b.val) hab⟩

end IntegrationInACVF.Section7
