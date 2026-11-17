module

public import IntegrationSection6.MixedCoordinatePointMaps

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Coordinate-block substitution and existential VF projection for
original-Gamma predicates, without enlarging their parameter base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {n m u w : ℕ}

theorem gamma_mixed_coordinate_preimage {A : Set (Point (M := M) u w)}
    (hA : GammaSetDefinable G A) (σ : Fin u → Fin n) (τ : Fin w → Fin m) :
    GammaSetDefinable G {p : Point (M := M) n m | (p.1 ∘ σ,p.2 ∘ τ) ∈ A} := by
  have h := (gammaLogicInput G).preimage_real (mixedCoordinatePointMap σ τ G.real) hA
  convert h using 1
  ext p
  constructor
  · intro hp
    exact ⟨⟨p,Set.mem_univ _⟩,rfl,hp⟩
  · rintro ⟨a,rfl,ha⟩
    exact ha

theorem gamma_exists_vf_coordinates {A : Set (Point (M := M) n m)}
    (hA : GammaSetDefinable G A) :
    GammaSetDefinable G {p : Point (M := M) 0 m | ∃ x : Fin n → VF (M := M), (x,p.2) ∈ A} := by
  have h := (gammaLogicInput G).image_real
    (mixedCoordinatePointMap (Fin.elim0 : Fin 0 → Fin n) (id : Fin m → Fin m) G.real) hA
  convert h using 1
  ext p
  constructor
  · rintro ⟨x,hx⟩
    exact ⟨⟨(x,p.2),Set.mem_univ _⟩,hx,Prod.ext (by funext i; exact i.elim0) rfl⟩
  · rintro ⟨a,ha,he⟩
    have ht := congrArg Prod.snd he
    exact ⟨a.val.1,ht ▸ ha⟩

end IntegrationInACVF.Section7
