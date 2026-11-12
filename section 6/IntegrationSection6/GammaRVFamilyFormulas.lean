import IntegrationSection6.GammaMixedTupleGraphs
import IntegrationSection6.GammaFiniteObjectSchemata

/-! Uniform original-Gamma domain/volume formulas over a VF parameter
block. Functionality and finite fibres are certified by the separate finite
schema validity predicate, rather than assumed for arbitrary rows. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a k : ℕ}

theorem gammaMixedRawGraph_append_iff
    (r : Point (M := M) p a → Point (M := M) 0 k → Prop)
    (x : Point (M := M) p a) (y : Point (M := M) 0 k) :
    Fin.append (gammaPointCode x) (fun j => (y.2 j).val) ∈ gammaMixedRawGraph r ↔ r x y := by
  constructor
  · rintro ⟨x',y',hr,he⟩
    have hx : x' = x := gammaPointCode_injective (funext (fun j => by
      simpa only [Fin.append_left] using congrFun he (Fin.castAdd k j)))
    have hy : y' = y := pureRVPoint_raw_injective (funext (fun j => by
      simpa only [Fin.append_right] using congrFun he (Fin.natAdd (p+a) j)))
    exact hx ▸ hy ▸ hr
  · exact fun hr => ⟨x,y,hr,rfl⟩

structure GammaRVFamilyFormula (B : Base (M := M)) (p a k : ℕ) where
  domain : Set (Point (M := M) p a)
  domain_definable : GammaSetDefinable B domain
  volume : Point (M := M) p a → Point (M := M) 0 k → Prop
  volume_definable : GammaGraphDefinable B volume

def GammaFiniteRVSchema.toFamily (F : GammaFiniteRVSchema B p a k) : GammaRVFamilyFormula B p a k where
  domain := {x | gammaPointCode x ∈ F.domain}
  domain_definable := gamma_set_of_sorted_formula F.domain_definable
  volume := fun x y => Fin.append (gammaPointCode x) (fun j => (y.2 j).val) ∈ F.volume
  volume_definable := gamma_mixed_rv_graph_from_tuple_formula F.volume_definable

def GammaRVFamilyFormula.schema (F : GammaRVFamilyFormula B p a k) (N : ℕ) : GammaFiniteRVSchema B p a k where
  domain := gammaPointCode '' F.domain
  volume := gammaMixedRawGraph F.volume
  domain_definable := F.domain_definable
  volume_definable := gammaMixedRawGraph_definable F.volume_definable
  bound := N

theorem GammaRVFamilyFormula.schema_domain (F : GammaRVFamilyFormula B p a k) (N : ℕ)
    (x : Point (M := M) p a) : gammaPointCode x ∈ (F.schema N).domain ↔ x ∈ F.domain := by
  constructor
  · rintro ⟨x',hx',he⟩
    exact gammaPointCode_injective he ▸ hx'
  · exact fun hx => ⟨x,hx,rfl⟩

theorem GammaRVFamilyFormula.schema_volume (F : GammaRVFamilyFormula B p a k) (N : ℕ)
    (x : Point (M := M) p a) (y : Point (M := M) 0 k) :
    Fin.append (gammaPointCode x) (fun j => (y.2 j).val) ∈ (F.schema N).volume ↔ F.volume x y :=
  gammaMixedRawGraph_append_iff F.volume x y

end IntegrationInACVF.Section6
