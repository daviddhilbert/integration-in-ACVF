import Integration7.RVLabelConstraintHeadProducts
import IntegrationSection5.GammaGraphOperations

/-! A map uniquely determined by equality of two finite RV-coordinate
selectors has its full graph over the original Gamma base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S : Set M} {a b d : ℕ}

theorem gamma_coordinate_square_graph
    {A : DefSet (M := M) S 0 a} {B : DefSet (M := M) S 0 b}
    (hA : GammaSetDefinable G (carrier A)) (hB : GammaSetDefinable G (carrier B))
    (f : Map A B) (ρ : Fin d → Fin a) (τ : Fin d → Fin b)
    (hSquare : ∀ p, p.val.2 ∘ ρ = (f p).val.2 ∘ τ)
    (hInjective : ∀ p q : B, p.val.2 ∘ τ = q.val.2 ∘ τ → p = q) :
    GammaGraphDefinable G (pointMapGraph f) := by
  let α := rvCoordinatePointMap ρ G.real
  let β := rvCoordinatePointMap τ G.real
  let L := gammaLogicInput G
  apply GammaGraphDefinable.congr (L.comp_graph (L.restrict_graph hA (L.real_map_graph α))
    (L.swap_graph (L.restrict_graph hB (L.real_map_graph β))))
  intro p q
  constructor
  · rintro ⟨z,⟨hp,a,ha,haz⟩,⟨hq,b,hb,hbz⟩⟩
    let u : A := ⟨p,hp⟩
    let v : B := ⟨q,hq⟩
    have hKey : u.val.2 ∘ ρ = v.val.2 ∘ τ := by
      have h := congrArg (fun z : Point (M := M) 0 d => z.2) (haz.trans hbz.symm)
      change a.val.2 ∘ ρ = b.val.2 ∘ τ at h
      rw [ha,hb] at h
      exact h
    have he : f u = v := hInjective _ _ ((hSquare u).symm.trans hKey)
    exact ⟨u,rfl,congrArg Subtype.val he⟩
  · rintro ⟨u,rfl,hq⟩
    let v := f u
    have hqB : q ∈ carrier B := (congrArg (fun z => z ∈ carrier B) hq).mp v.property
    let uReal : PresentedSet.univ (pointSpace (M := M) 0 a) G.real := ⟨u.val,Set.mem_univ _⟩
    let vReal : PresentedSet.univ (pointSpace (M := M) 0 b) G.real := ⟨q,Set.mem_univ _⟩
    refine ⟨(α uReal).val,⟨u.property,uReal,rfl,rfl⟩,hqB,vReal,rfl,?_⟩
    apply Prod.ext (Subsingleton.elim _ _)
    change q.2 ∘ τ = u.val.2 ∘ ρ
    exact (congrArg (fun z : Point (M := M) 0 b => z.2 ∘ τ) hq).symm.trans (hSquare u).symm

end IntegrationInACVF.Section7
