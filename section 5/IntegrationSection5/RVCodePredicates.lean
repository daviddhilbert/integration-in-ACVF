import IntegrationSection4.GammaRVMapOperations
import Section5.GammaLiftRelation

/-! Original-Gamma selection and equality predicates for actual finite RV
codes. These operations retain full graphs and do not choose representatives. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
open IntegrationInACVF.Section4
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {n m d e : ℕ} {A : Set (Point (M := M) n m)}

def selectRVCode (Q : GammaRVMap G A d) (ρ : Fin e → Fin d) : GammaRVMap G A e where
  toFun a := Q.toFun a ∘ ρ
  graph := by
    let F := rvCoordinatePointMap (M := M) ρ G.real
    have h := (gammaLogicInput G).comp_graph Q.graph ((gammaLogicInput G).real_map_graph F)
    apply GammaGraphDefinable.congr h
    intro p q
    constructor
    · rintro ⟨z,⟨a,ha,haz⟩,b,hbz,hbq⟩
      refine ⟨a,ha,?_⟩
      have hb : b.val.2 = Q.toFun a := (congrArg Prod.snd hbz).trans haz.symm
      exact (congrArg (fun t => t ∘ ρ) hb).symm.trans (congrArg Prod.snd hbq)
    · rintro ⟨a,ha,hq⟩
      refine ⟨(Fin.elim0,Q.toFun a),⟨a,ha,rfl⟩,
        ⟨(Fin.elim0,Q.toFun a),Set.mem_univ _⟩,rfl,?_⟩
      exact Prod.ext (Subsingleton.elim _ _) hq

def rvCodeEqualizer (P Q : GammaRVMap G A d) : Set (Point (M := M) n m) :=
  {p | ∃ a : A, a.val = p ∧ P.toFun a = Q.toFun a}

theorem rvCodeEqualizer_definable (P Q : GammaRVMap G A d) :
    GammaSetDefinable G (rvCodeEqualizer P Q) := by
  have h := (gammaLogicInput G).image_graph ((gammaLogicInput G).swap_graph
    (GammaGraphOperations.inter G P.graph Q.graph))
  convert h using 1
  ext p
  constructor
  · rintro ⟨a,ha,hPQ⟩
    exact ⟨(Fin.elim0,P.toFun a),⟨a,ha,rfl⟩,⟨a,ha,hPQ.symm⟩⟩
  · rintro ⟨q,⟨a,ha,hP⟩,⟨b,hb,hQ⟩⟩
    have hab : b = a := Subtype.ext (hb.trans ha.symm)
    subst b
    exact ⟨a,ha,hP.trans hQ.symm⟩

end IntegrationInACVF.Section5
