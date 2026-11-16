module

public import Integration7.GammaRVMapRestrictions
public import Integration7.ElementaryBlowupConstruction
public import IntegrationSection6.GammaElementaryDomains

@[expose] public section

/-! The actual packed RV product and blowup cone have their full Gamma
domains. The cone comparison uses the canonical structure explicitly. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaSetDefinable gammaLogicInput rvCoordinatePointMap)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {a b : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

theorem gamma_actual_rv_product_domain
    (A : DefSet (rawRVSpace (M := M) a) S) (D : DefSet (rawRVSpace (M := M) b) S)
    (hA : GammaSetDefinable B {p : Point (M := M) 0 a | p.2 ∈ A.carrier})
    (hD : GammaSetDefinable B {p : Point (M := M) 0 b | p.2 ∈ D.carrier}) :
    GammaSetDefinable B {p : Point (M := M) 0 (a+b) | p.2 ∈ (rvProductDomain A D).carrier} := by
  have hl := (gammaLogicInput B).preimage_real (rvCoordinatePointMap (Fin.castAdd b) B.real) hA
  have hr := (gammaLogicInput B).preimage_real (rvCoordinatePointMap (Fin.natAdd a) B.real) hD
  convert (gammaLogicInput B).inter hl hr using 1
  ext p
  constructor
  · intro hp
    obtain ⟨u,hu,v,hv,hp⟩ := (mem_rvProductDomain A D p.2).mp hp
    have hleft : (fun j => p.2 (Fin.castAdd b j)) = u := by
      funext j
      exact (congrFun hp (Fin.castAdd b j)).symm.trans (Fin.append_left _ _ j)
    have hright : (fun j => p.2 (Fin.natAdd a j)) = v := by
      funext j
      exact (congrFun hp (Fin.natAdd a j)).symm.trans (Fin.append_right _ _ j)
    refine ⟨⟨⟨p,Set.mem_univ _⟩,rfl,?_⟩,⟨⟨p,Set.mem_univ _⟩,rfl,?_⟩⟩
    · exact (congrArg (fun r => r ∈ A.carrier) hleft).mpr hu
    · exact (congrArg (fun r => r ∈ D.carrier) hright).mpr hv
  · rintro ⟨⟨x,hx,hu⟩,⟨y,hy,hv⟩⟩
    change (fun j => x.val.2 (Fin.castAdd b j)) ∈ A.carrier at hu
    change (fun j => y.val.2 (Fin.natAdd a j)) ∈ D.carrier at hv
    rw [hx] at hu
    rw [hy] at hv
    apply (mem_rvProductDomain A D p.2).mpr
    refine ⟨_,hu,_,hv,?_⟩
    funext j
    cases j using Fin.addCases <;> simp only [rvAppend,Fin.append_left,Fin.append_right]

theorem gamma_actual_blowup_cone
    (hc : CanonicalStructure.IsCanonical (M := M)) :
    GammaSetDefinable B {p : Point (M := M) 0 1 | p.2 ∈ (blowupConeSet (M := M) S).carrier} := by
  have h : GammaSetDefinable B {p : Point (M := M) 0 1 |
      p.2 ∈ @DefSet.carrier LRV M N _ B.real (@Section6.positiveRV M N B.real)} := gamma_positiveRV
  convert h using 1
  ext p
  change (¬ @iLe M sM (p.2 0).val (@iRVOne M sM)) ↔
    ¬ @iLe M N (p.2 0).val (@iRVOne M N)
  rw [SpecialTransformations.Section8.normalize_eq_of_isCanonical hc]

end IntegrationInACVF.Section7
