module

public import Integration7.IndependentRVConstraintHeadMaps
public import Integration7.RawRVProductTransfers
public import Integration7.CanonicalVolumePresentations
public import Integration7.GammaRVMapRestrictions

@[expose] public section

/-! The independent RV-factor head bijection on actual raw labels,
with its exact two coordinate blocks and original Gamma certificate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Milestone0.sortEval SpecialTransformations.Section4.realSpace
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {S : Set M} {a b d : ℕ}
variable {A : DefSet (M := M) S 1 a} {B : DefSet (M := M) S 1 b}
variable {T : SpecialBijection A B} {H : DefSet (M := M) S 1 (a+d)} {Q : DefSet (M := M) S 0 (a+d)}
namespace RVLabelConstraintSpecialPreparation

def rawIndependentHeadProductMap (L : RVLabelConstraintSpecialPreparation T H Q (Fin.castAdd d) P)
    (R : DefSet (M := M) S 0 d)
    (hQ : ∀ q : Point (M := M) 0 (a+d), q ∈ carrier Q ↔ (Fin.elim0,q.2 ∘ Fin.natAdd a) ∈ carrier R) :=
  rawRVProductTransfer (L.independentHeadProductMap R hQ)

theorem raw_independent_head_product_map_bijective
    (L : RVLabelConstraintSpecialPreparation T H Q (Fin.castAdd d) P)
    (R : DefSet (M := M) S 0 d)
    (hQ : ∀ q : Point (M := M) 0 (a+d), q ∈ carrier Q ↔ (Fin.elim0,q.2 ∘ Fin.natAdd a) ∈ carrier R) :
    Function.Bijective (L.rawIndependentHeadProductMap R hQ) :=
  raw_rv_product_transfer_bijective _ (L.independent_head_product_map_bijective R hQ)

theorem raw_independent_head_product_map_value
    (L : RVLabelConstraintSpecialPreparation T H Q (Fin.castAdd d) P)
    (R : DefSet (M := M) S 0 d)
    (hQ : ∀ q : Point (M := M) 0 (a+d), q ∈ carrier Q ↔ (Fin.elim0,q.2 ∘ Fin.natAdd a) ∈ carrier R)
    (u : Map.image (rawLabelMap (headImage L.target))) :
    (L.rawIndependentHeadProductMap R hQ u).val =
      Fin.append (u.val ∘ L.headParameters ∘ Fin.natAdd a) (u.val ∘ L.headProjection) := by
  obtain ⟨p,hp⟩ := u.property
  have he : u = Map.toImage (rawLabelMap (headImage L.target)) p := Subtype.ext hp.symm
  subst u
  exact raw_rv_product_transfer_value (L.independentHeadProductMap R hQ) p

def canonicalIndependentHeadProductMap (hc : CanonicalStructure.IsCanonical (M := M))
    (L : RVLabelConstraintSpecialPreparation T H Q (Fin.castAdd d) P)
    (R : DefSet (M := M) S 0 d)
    (hQ : ∀ q : Point (M := M) 0 (a+d), q ∈ carrier Q ↔ (Fin.elim0,q.2 ∘ Fin.natAdd a) ∈ carrier R) :=
  canonicalRawRVMap hc (L.rawIndependentHeadProductMap R hQ)

theorem canonical_independent_head_product_map_bijective
    (hc : CanonicalStructure.IsCanonical (M := M))
    (L : RVLabelConstraintSpecialPreparation T H Q (Fin.castAdd d) P)
    (R : DefSet (M := M) S 0 d)
    (hQ : ∀ q : Point (M := M) 0 (a+d), q ∈ carrier Q ↔ (Fin.elim0,q.2 ∘ Fin.natAdd a) ∈ carrier R) :
    Function.Bijective (L.canonicalIndependentHeadProductMap hc R hQ) := by
  constructor
  · intro u v he
    have h := (L.raw_independent_head_product_map_bijective R hQ).1 (Subtype.ext (congrArg Subtype.val he))
    exact Subtype.ext (congrArg Subtype.val h)
  · intro v
    obtain ⟨u,hu⟩ := (L.raw_independent_head_product_map_bijective R hQ).2 ⟨v.val,v.property⟩
    exact ⟨⟨u.val,u.property⟩,Subtype.ext (congrArg Subtype.val hu)⟩

theorem canonical_independent_head_product_map_gamma
    (hc : CanonicalStructure.IsCanonical (M := M))
    (L : RVLabelConstraintSpecialPreparation T H Q (Fin.castAdd d) P)
    (R : DefSet (M := M) S 0 d)
    (hQ : ∀ q : Point (M := M) 0 (a+d), q ∈ carrier Q ↔ (Fin.elim0,q.2 ∘ Fin.natAdd a) ∈ carrier R) :
    RVMapGamma (L.canonicalIndependentHeadProductMap hc R hQ) P := by
  have hSource : GammaSetDefinable P {p : Point (M := M) 0 (1+L.arity) |
      p.2 ∈ (canonicalRawRVDomain hc (Map.image (rawLabelMap (headImage L.target)))).carrier} := by
    convert gamma_headImage L.target (L.gamma.target P L.special.chain) using 1
    ext p
    constructor
    · rintro ⟨q,hq⟩
      have he : q.val=p := Prod.ext (Subsingleton.elim _ _) hq
      exact he ▸ q.property
    · intro hp
      exact ⟨⟨p,hp⟩,rfl⟩
  apply gamma_real_rv_map_graph hc P _ (rvCoordinateSelectMap P.real
    (Fin.append (L.headParameters ∘ Fin.natAdd a) L.headProjection)) hSource
  intro u
  have h := L.raw_independent_head_product_map_value R hQ ⟨u.val,u.property⟩
  exact h.trans (by
    change Fin.append (u.val ∘ L.headParameters ∘ Fin.natAdd a) (u.val ∘ L.headProjection) =
      u.val ∘ Fin.append (L.headParameters ∘ Fin.natAdd a) L.headProjection
    funext j
    cases j using Fin.addCases <;> simp only [Function.comp_apply,Fin.append_left,Fin.append_right])
end RVLabelConstraintSpecialPreparation
end IntegrationInACVF.Section7
