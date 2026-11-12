import IntegrationSection6.FiniteRVParameterExtension
import IntegrationSection6.FiniteGammaIsoLaws

/-! Original-Gamma RV[k] data at a fixed internal real presentation.
The parameter set S describes codes only; every domain and volume graph
is still certified over the original Base B. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

variable {B : Base (M := M)} {S : Set M} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

structure GammaObjectAt (B : Base (M := M)) (S : Set M) (n : ℕ) where
  object : @RVFiniteObject M N S n
  real_contains : B.real ⊆ S
  domain_graph : GammaSetDefinable B
    {p : Point (M := M) 0 (rvObjectArity object.obj) | p.2 ∈ carrier (rvObjectDomain object.obj)}
  volume_graph : GammaGraphDefinable B
    (fun (p : Point (M := M) 0 (rvObjectArity object.obj)) (q : Point (M := M) 0 n) =>
      ∃ u : rvObjectDomain object.obj, u.val = p.2 ∧ (rvObjectVolume object.obj u).val = q.2)

def GammaObjectAt.toGamma (U : GammaObjectAt B S n) : GammaRVFiniteObject B n where
  codes := S
  real_contains := U.real_contains
  object := U.object.obj
  domain_graph := U.domain_graph
  volume_graph := U.volume_graph
  finite_volume := U.object.property

def gammaObjectAtExtend (U : GammaRVFiniteObject B n) (hUS : U.codes ⊆ S) : GammaObjectAt B S n where
  object := @extendObject M N U.codes S n hUS (ofGamma U)
  real_contains := fun x hx => hUS (U.real_contains hx)
  domain_graph := U.domain_graph
  volume_graph := U.volume_graph

def gammaPullbackAt (hBS : B.real ⊆ S) {m : ℕ}
    (A : SpecialTransformations.Section5.DefSet (M := M) S n m)
    (hA : GammaSetDefinable B (carrier A))
    (hfin : Map.FiniteFibres (rvObjectVolume (pullbackObject A))) : GammaObjectAt B S n where
  object := ⟨pullbackObject A,hfin⟩
  real_contains := hBS
  domain_graph := gamma_pullback_domain (gammaLogicInput B) A hA
  volume_graph := (gammaPullbackObject (gammaLogicInput B) hBS A hA).volume_graph

@[simp] theorem gammaObjectAtExtend_domain (U : GammaRVFiniteObject B n) (hUS : U.codes ⊆ S) :
    carrier (rvObjectDomain (gammaObjectAtExtend U hUS).object.obj) = carrier (rvObjectDomain U.object) := rfl

end IntegrationInACVF.Section6.FiniteRV
