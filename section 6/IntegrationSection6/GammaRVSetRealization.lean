import IntegrationSection6.GammaRVRealization

/-! A full Gamma RV set has a real presentation after naming only the
finite representative tuple used in its invariant formula. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {a : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

theorem gamma_rv_set_real_specialize (D : Set (Fin a → RV (M := M)))
    (hD : GammaSetDefinable B {p : Point (M := M) 0 a | p.2 ∈ D}) :
    ∃ d, ∃ t : Fin d → Code (M := M),
      @SpecialTransformations.DefinableGeometry.Space.Definable LRV M N
        (@SpecialTransformations.Section4.rawRVSpace M N a) (B.real ∪ Set.range (rawTuple t)) D := by
  let Z := PresentedSet.univ (pointSpace (M := M) 0 a) B.real
  have h := (gammaLogicInput B).restrict_graph hD ((gammaLogicInput B).real_map_graph (Map.id Z))
  obtain ⟨d,t,hr⟩ := gamma_rv_relation_real_specialize h
  have hd := @SpecialTransformations.DefinableGeometry.Space.RelationDefinable.exists_right LRV M N
    (@SpecialTransformations.Section4.rawRVSpace M N a) (@SpecialTransformations.Section4.rawRVSpace M N a)
    (B.real ∪ Set.range (rawTuple t)) _ hr
  refine ⟨d,t,?_⟩
  convert hd using 1
  ext x
  constructor
  · intro hx
    exact ⟨x,hx,⟨(Fin.elim0,x),Set.mem_univ _⟩,rfl,rfl⟩
  · rintro ⟨y,hx,_⟩
    exact hx

end IntegrationInACVF.Section6
