import Integration7.GammaNamedZeroPresentation
import Integration7.HKVolumeCoproductIsomorphisms
import Integration7.GammaTaggedRVMapGraphs
import Integration7.GammaRVTagMaps

/-! Gamma degree-zero RV coproducts and the additive monoid of Gamma-named
degree-zero RV classes. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {B : Base (M := M)} {S : Set M}

theorem ZeroRVVolumeObject.Gamma.volume {U : ZeroRVVolumeObject (M := M) S} (hU : U.Gamma B) :
    RVMapGamma U.underlying.obj.volume B := by
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr
    ((gammaLogicInput B).restrict_graph hU.domain (GammaLift.gamma_true_graph (B := B) (c := 0) (d := 0)))
  intro p q
  constructor
  · rintro ⟨hp, -⟩
    exact ⟨⟨p.2, hp⟩, rfl, funext (fun i => Fin.elim0 i)⟩
  · rintro ⟨u, hu, -⟩
    refine ⟨?_, trivial⟩
    change p.2 ∈ U.underlying.obj.domain.carrier
    rw [← hu]
    exact u.property

theorem ZeroRVVolumeObject.Gamma.coprod {U V : ZeroRVVolumeObject (M := M) S}
    (hU : U.Gamma B) (hV : V.Gamma B) : (coprod S 0 U V).Gamma B := by
  refine ⟨?_, ?_⟩
  · exact (gamma_tagged_rv_map_graph U.underlying.obj V.underlying.obj _ _ _ hU.volume hV.volume
      (fun u => rvCoprod_value_left U.underlying.obj V.underlying.obj u)
      (fun v => rvCoprod_value_right U.underlying.obj V.underlying.obj v)).domain
  · apply gamma_tagged_rv_map_graph U.underlying.obj V.underlying.obj _ _ _ hU.density hV.density
    · intro u
      funext j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      exact coprod_density_left 0 U V u
    · intro v
      funext j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      exact coprod_density_right 0 U V v

theorem zero_empty_gamma (S : Set M) : (empty S 0).Gamma B := by
  refine ⟨?_, ?_⟩
  · have h := (gammaLogicInput B).sdiff (GammaLift.gamma_univ_set (B := B) (a := 0)
      (b := (empty (M := M) S 0).underlying.obj.arity)) GammaLift.gamma_univ_set
    convert h using 1
    ext p
    constructor
    · intro hp
      exact False.elim hp
    · rintro ⟨-, h⟩
      exact False.elim (h (Set.mem_univ _))
  · apply SpecialTransformations.Section5.GammaGraphDefinable.congr (FiniteRV.gamma_empty_graph (B := B) _ _)
    intro p q
    constructor
    · exact False.elim
    · rintro ⟨u, _, _⟩
      exact False.elim u.property

theorem zero_coprod_iso_gamma (hc : CanonicalStructure.IsCanonical (M := M)) {U U' V V' : ZeroRVVolumeObject (M := M) S}
    (hU : U.Gamma B) (hV : V.Gamma B) (hU' : U'.Gamma B) (hV' : V'.Gamma B)
    {f : ZeroRVVolumeIso U U'} {g : ZeroRVVolumeIso V V'} (hf : f.GammaDefinable B) (hg : g.GammaDefinable B) :
    (zeroCoprodIso f g).GammaDefinable B := by
  apply gamma_tagged_rv_map_graph U.underlying.obj V.underlying.obj _
    ((rvLeftTagMap U'.underlying.obj.domain V'.underlying.obj.arity).comp (finiteIsoMap f.iso))
    ((rvRightTagMap V'.underlying.obj.domain U'.underlying.obj.arity).comp (finiteIsoMap g.iso))
    (RVMapGamma.comp hf (gamma_rv_left_tag_map hc _ _ hU'.domain))
    (RVMapGamma.comp hg (gamma_rv_right_tag_map hc _ _ hV'.domain))
  · intro u
    exact congrArg Subtype.val (rvCoprodIsoExplicit_left _ _ u)
  · intro v
    exact congrArg Subtype.val (rvCoprodIsoExplicit_right _ _ v)

theorem zero_coprod_swap_gamma (hc : CanonicalStructure.IsCanonical (M := M)) {U V : ZeroRVVolumeObject (M := M) S} (hU : U.Gamma B) (hV : V.Gamma B) :
    (zeroCoprodSwap U V).GammaDefinable B :=
  gamma_tagged_rv_map_graph U.underlying.obj V.underlying.obj _
    (rvRightTagMap U.underlying.obj.domain V.underlying.obj.arity)
    (rvLeftTagMap V.underlying.obj.domain U.underlying.obj.arity)
    (gamma_rv_right_tag_map hc _ _ hU.domain)
    (gamma_rv_left_tag_map hc _ _ hV.domain)
    (fun u => congrArg Subtype.val (rvCoprodSwapExplicit_left U.underlying.obj V.underlying.obj u))
    (fun v => congrArg Subtype.val (rvCoprodSwapExplicit_right U.underlying.obj V.underlying.obj v))

theorem zero_coprod_assoc_gamma (hc : CanonicalStructure.IsCanonical (M := M)) {U V W : ZeroRVVolumeObject (M := M) S}
    (hU : U.Gamma B) (hV : V.Gamma B) (hW : W.Gamma B) :
    (zeroCoprodAssoc U V W).GammaDefinable B := by
  let F := (rvCoprodAssocExplicit U.underlying.obj V.underlying.obj W.underlying.obj).hom.map
  let VW := coprod S 0 V W
  let fl := F.comp (rvCoprodLeftMap (coprod S 0 U V).underlying.obj W.underlying.obj)
  let outer := rvRightTagMap VW.underlying.obj.domain U.underlying.obj.arity
  have hOuter : RVMapGamma outer B := gamma_rv_right_tag_map hc _ _ (hV.coprod hW).domain
  have hVleft : RVMapGamma (rvCoprodLeftMap V.underlying.obj W.underlying.obj) B :=
    (gamma_rv_left_tag_map hc _ _ hV.domain).congr (fun _ => rfl)
  have hWright : RVMapGamma (rvCoprodRightMap V.underlying.obj W.underlying.obj) B :=
    (gamma_rv_right_tag_map hc _ _ hW.domain).congr (fun _ => rfl)
  have hfl : RVMapGamma fl B := by
    apply gamma_tagged_rv_map_graph U.underlying.obj V.underlying.obj fl
      (rvLeftTagMap U.underlying.obj.domain VW.underlying.obj.arity)
      (outer.comp (rvCoprodLeftMap V.underlying.obj W.underlying.obj))
      (gamma_rv_left_tag_map hc _ _ hU.domain) (hVleft.comp hOuter)
    · intro u
      exact congrArg Subtype.val (rvCoprodAssocExplicit_left U.underlying.obj V.underlying.obj W.underlying.obj u)
    · intro v
      exact congrArg Subtype.val (rvCoprodAssocExplicit_middle U.underlying.obj V.underlying.obj W.underlying.obj v)
  apply gamma_tagged_rv_map_graph (coprod S 0 U V).underlying.obj W.underlying.obj F
    fl.toUniv (outer.comp (rvCoprodRightMap V.underlying.obj W.underlying.obj))
    (hfl.congr (fun _ => rfl)) (hWright.comp hOuter)
  · intro u
    rfl
  · intro w
    exact congrArg Subtype.val (rvCoprodAssocExplicit_right U.underlying.obj V.underlying.obj W.underlying.obj w)

theorem zero_coprod_empty_embedding_gamma (hc : CanonicalStructure.IsCanonical (M := M)) {U : ZeroRVVolumeObject (M := M) S} (hU : U.Gamma B) :
    (zeroCoprodEmptyEmbedding U).GammaDefinable B :=
  (gamma_rv_left_tag_map hc U.underlying.obj.domain (empty (M := M) S 0).underlying.obj.arity hU.domain).congr
    (fun _ => rfl)

def GammaZeroRVObjects.coprod (U V : GammaZeroRVObjects B S) : GammaZeroRVObjects B S :=
  ⟨IntegrationInACVF.Section7.HK.coprod S 0 U.val V.val, U.property.coprod V.property⟩

def gammaZeroRVClassesAdd (hc : CanonicalStructure.IsCanonical (M := M)) : Add (GammaZeroRVClasses B S) :=
  ⟨Quotient.map₂ GammaZeroRVObjects.coprod (fun U U' ⟨f, hf⟩ V V' ⟨g, hg⟩ =>
    ⟨zeroCoprodIso f g, zero_coprod_iso_gamma hc U.property V.property U'.property V'.property hf hg⟩)⟩

def gammaZeroRVClass (U : GammaZeroRVObjects B S) : GammaZeroRVClasses B S := Quotient.mk _ U

theorem gammaZeroRVClass_iso {U V : GammaZeroRVObjects B S} (e : ZeroRVVolumeIso U.val V.val)
    (he : e.GammaDefinable B) : gammaZeroRVClass U = gammaZeroRVClass V :=
  Quotient.sound ⟨e, he⟩

/-- The additive monoid of Gamma-named degree-zero RV classes (actual coproducts). -/
def gammaZeroRVAddCommMonoid (hc : CanonicalStructure.IsCanonical (M := M)) :
    AddCommMonoid (GammaZeroRVClasses B S) :=
  letI := gammaZeroRVClassesAdd (B := B) (S := S) hc
  letI : Zero (GammaZeroRVClasses B S) := ⟨gammaZeroRVClass ⟨empty S 0, zero_empty_gamma S⟩⟩
  { add_assoc := fun a b c => Quotient.inductionOn₃ a b c (fun U V W =>
      gammaZeroRVClass_iso (zeroCoprodAssoc U.val V.val W.val)
        (zero_coprod_assoc_gamma hc U.property V.property W.property))
    add_comm := fun a b => Quotient.inductionOn₂ a b (fun U V =>
      gammaZeroRVClass_iso (zeroCoprodSwap U.val V.val) (zero_coprod_swap_gamma hc U.property V.property))
    add_zero := fun a => Quotient.inductionOn a (fun U =>
      gammaZeroRVClass_iso (zeroCoprodEmptyEmbedding U.val).symm
        (zero_coprod_empty_embedding_gamma hc U.property).symm)
    zero_add := fun a => Quotient.inductionOn a (fun U =>
      gammaZeroRVClass_iso ((zeroCoprodSwap _ U.val).trans (zeroCoprodEmptyEmbedding U.val).symm)
        ((zero_coprod_swap_gamma hc (zero_empty_gamma S) U.property).trans
          (zero_coprod_empty_embedding_gamma hc U.property).symm))
    nsmul := nsmulRec }

end IntegrationInACVF.Section7.HK
