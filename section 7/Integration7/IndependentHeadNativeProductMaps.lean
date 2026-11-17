module

public import Integration7.IndependentRVRawHeadProducts
public import Integration7.CanonicalUnaryHeadProducts
public import Integration7.NativeVolumeDomains

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The checked independent head bijection acts on the literal native
RV label domains used by the actual coordinate-density volume objects. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point carrier headImage SpecialBijection)
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {S : Set M} {a b d : ℕ}
variable {A : SpecialTransformations.Section5.DefSet (M := M) S 1 a}
variable {B : SpecialTransformations.Section5.DefSet (M := M) S 1 b}
variable {T : SpecialBijection A B} {H : SpecialTransformations.Section5.DefSet (M := M) S 1 (a+d)}
variable {Q : SpecialTransformations.Section5.DefSet (M := M) S 0 (a+d)}
namespace RVLabelConstraintSpecialPreparation

private theorem output_carrier (hc : CanonicalStructure.IsCanonical (M := M))
    (R : SpecialTransformations.Section5.DefSet (M := M) S 0 d) :
    (canonicalRawRVDomain hc (@rvProductDomain M (@CanonicalStructure.normalize M sM) S d (1+b)
      (SpecialTransformations.Section5.Map.image (rawLabelMap R))
      (SpecialTransformations.Section5.Map.image (rawLabelMap (headImage B))))).carrier =
      (rvProductDomain (rawVolumeContractionLabels hc R) (rawVolumeContractionLabels hc (headImage B))).carrier := by
  exact canonical_rv_product_domain_carrier hc _ _

def nativeIndependentHeadProductMap (hc : CanonicalStructure.IsCanonical (M := M))
    (L : RVLabelConstraintSpecialPreparation T H Q (Fin.castAdd d) P)
    (R : SpecialTransformations.Section5.DefSet (M := M) S 0 d)
    (hQ : ∀ q : Point (M := M) 0 (a+d), q ∈ carrier Q ↔ (Fin.elim0,q.2 ∘ Fin.natAdd a) ∈ carrier R) :
    Map (rawVolumeContractionLabels hc (headImage L.target))
      (rvProductDomain (rawVolumeContractionLabels hc R) (rawVolumeContractionLabels hc (headImage B))) := by
  let f := L.canonicalIndependentHeadProductMap hc R hQ
  let i : Map (rawVolumeContractionLabels hc (headImage L.target)) _ := Map.inclusion (fun _ h => h)
  let j : Map _ (rvProductDomain (rawVolumeContractionLabels hc R) (rawVolumeContractionLabels hc (headImage B))) :=
    Map.inclusion (output_carrier hc R).le
  exact j.comp (f.comp i)

theorem native_independent_head_product_map_bijective (hc : CanonicalStructure.IsCanonical (M := M))
    (L : RVLabelConstraintSpecialPreparation T H Q (Fin.castAdd d) P)
    (R : SpecialTransformations.Section5.DefSet (M := M) S 0 d)
    (hQ : ∀ q : Point (M := M) 0 (a+d), q ∈ carrier Q ↔ (Fin.elim0,q.2 ∘ Fin.natAdd a) ∈ carrier R) :
    Function.Bijective (L.nativeIndependentHeadProductMap hc R hQ) := by
  have hf := L.canonical_independent_head_product_map_bijective hc R hQ
  constructor
  · intro u v he
    exact Subtype.ext (congrArg Subtype.val (hf.1 (Subtype.ext (congrArg Subtype.val he))))
  · intro v
    obtain ⟨u,hu⟩ := hf.2 ⟨v.val,(output_carrier hc R).ge v.property⟩
    exact ⟨⟨u.val,u.property⟩,Subtype.ext (congrArg Subtype.val hu)⟩

theorem native_independent_head_product_map_value (hc : CanonicalStructure.IsCanonical (M := M))
    (L : RVLabelConstraintSpecialPreparation T H Q (Fin.castAdd d) P)
    (R : SpecialTransformations.Section5.DefSet (M := M) S 0 d)
    (hQ : ∀ q : Point (M := M) 0 (a+d), q ∈ carrier Q ↔ (Fin.elim0,q.2 ∘ Fin.natAdd a) ∈ carrier R)
    (u : rawVolumeContractionLabels hc (headImage L.target)) :
    (L.nativeIndependentHeadProductMap hc R hQ u).val =
      Fin.append (u.val ∘ L.headParameters ∘ Fin.natAdd a) (u.val ∘ L.headProjection) :=
  L.raw_independent_head_product_map_value R hQ ⟨u.val,u.property⟩
end RVLabelConstraintSpecialPreparation
end IntegrationInACVF.Section7
