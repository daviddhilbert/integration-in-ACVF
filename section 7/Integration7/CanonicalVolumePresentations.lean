import Integration7.UniformVolumeData
import Section9.SpecialJacobianGeneric

/-! A canonical model has the same raw RV domains and maps before and
after normalization. These adapters retain points and parameter sets. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.Section8
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {a b : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

def canonicalRawRVDomain (hc : CanonicalStructure.IsCanonical (M := M))
    (A : @DefSet LRV M N (@rawRVSpace M N a) S) :
    DefSet (rawRVSpace (M := M) a) S := by
  let T := @Space.preimage LRV M N (@rawRVSpace M N a) (@DefSet.carrier LRV M N _ S A)
  have h : @Set.Definable M S LRV sM (Fin a) T :=
    Eq.mp (congrArg (fun I : LRV.Structure M =>
      @Set.Definable M S LRV I (Fin a) T) (normalize_eq_of_isCanonical hc)) (@DefSet.definable LRV M N _ S A)
  exact ⟨(@DefSet.carrier LRV M N _ S A),h⟩

@[simp] theorem canonicalRawRVDomain_carrier
    (hc : CanonicalStructure.IsCanonical (M := M))
    (A : @DefSet LRV M N (@rawRVSpace M N a) S) :
    (canonicalRawRVDomain hc A).carrier = (@DefSet.carrier LRV M N _ S A) := rfl

def canonicalRawRVMap (hc : CanonicalStructure.IsCanonical (M := M))
    {A : @DefSet LRV M N (@rawRVSpace M N a) S}
    {B : @DefSet LRV M N (@rawRVSpace M N b) S}
    (f : @Map LRV M N _ _ S A B) :
    Map (canonicalRawRVDomain hc A) (canonicalRawRVDomain hc B) := by
  let T := @Space.relation LRV M N (@rawRVSpace M N a) (@rawRVSpace M N b)
    (fun x y => ∃ u : A, u.val = x ∧ (f u).val = y)
  have h : @Set.Definable M S LRV sM (Fin a ⊕ Fin b) T :=
    Eq.mp (congrArg (fun I : LRV.Structure M =>
      @Set.Definable M S LRV I (Fin a ⊕ Fin b) T)
      (normalize_eq_of_isCanonical hc)) (@Map.graph_definable LRV M N _ _ S A B f)
  exact ⟨fun x => ⟨(f ⟨x.val,x.property⟩).val,(f ⟨x.val,x.property⟩).property⟩,h⟩

@[simp] theorem canonicalRawRVMap_value
    (hc : CanonicalStructure.IsCanonical (M := M))
    {A : @DefSet LRV M N (@rawRVSpace M N a) S}
    {B : @DefSet LRV M N (@rawRVSpace M N b) S}
    (f : @Map LRV M N _ _ S A B) (x : canonicalRawRVDomain hc A) :
    (canonicalRawRVMap hc f x).val = (f ⟨x.val,x.property⟩).val := rfl

end IntegrationInACVF.Section7
