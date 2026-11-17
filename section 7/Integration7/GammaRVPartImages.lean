module

public import Integration7.GammaRVParameterSelections

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! A definable union of whole parameter fibres is selected by its
actual RV image. This converts definable geometric cases into actual
parameter selections without choosing representatives. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section4.GammaRVMap
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {n m d : ℕ} {A : Set (Point (M := M) n m)}

def partImage (P : GammaRVMap G A d) (D : Set (Point (M := M) n m)) : Set (Point (M := M) 0 d) :=
  {q | ∃ a : A, a.val ∈ D ∧ P.toFun a = q.2}

theorem part_image_gamma (P : GammaRVMap G A d) {D : Set (Point (M := M) n m)}
    (hD : GammaSetDefinable G D) : GammaSetDefinable G (P.partImage D) := by
  have h := (gammaLogicInput G).image_graph ((gammaLogicInput G).restrict_graph hD P.graph)
  convert h using 1
  ext q
  constructor
  · rintro ⟨a,ha,hq⟩
    exact ⟨a.val,ha,a,rfl,hq⟩
  · rintro ⟨p,hp,a,rfl,hq⟩
    exact ⟨a,hp,hq⟩

theorem selected_part_image_eq (P : GammaRVMap G A d) (D : Set (Point (M := M) n m))
    (hDA : D ⊆ A) (hWhole : ∀ a b : A, P.toFun a = P.toFun b → a.val ∈ D → b.val ∈ D) :
    P.selectedDomain (P.partImage D) = D := by
  ext p
  constructor
  · rintro ⟨a,ha,b,hb,he⟩
    exact ha ▸ hWhole b a he hb
  · intro hp
    let a : A := ⟨p,hDA hp⟩
    exact ⟨a,rfl,a,hp,rfl⟩

end IntegrationInACVF.Section4.GammaRVMap
