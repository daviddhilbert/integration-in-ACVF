import Integration7.CanonicalVolumeSchemaRows
import Integration7.NondegenerateFiniteIso
import IntegrationSection6.GammaFamilyBijectionValidity
import Section4.FunctionalRelations

/-! Valid essential chart rows construct their actual definable bijection.
Only the coordinate graph interpretation and ordinary chart validity enter
this step; no volume-preserving equation is assumed. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {B : Base (M := M)} {p k a b : ℕ} {sp : Fin p → SortTag}

theorem canonicalRawRVRelation
    (hc : CanonicalStructure.IsCanonical (M := M))
    (R : (Fin a → CanonicalRV.RVSort M) → (Fin b → CanonicalRV.RVSort M) → Prop)
    (hR : @Space.RelationDefinable LRV M (@CanonicalStructure.normalize M sM)
      (@rawRVSpace M (@CanonicalStructure.normalize M sM) a)
      (@rawRVSpace M (@CanonicalStructure.normalize M sM) b) S R) :
    (rawRVSpace (M := M) a).RelationDefinable (rawRVSpace (M := M) b) S R := by
  let T := @Space.relation LRV M (@CanonicalStructure.normalize M sM)
    (@rawRVSpace M (@CanonicalStructure.normalize M sM) a)
    (@rawRVSpace M (@CanonicalStructure.normalize M sM) b) R
  exact Eq.mp (congrArg (fun I : LRV.Structure M => @Set.Definable M S LRV I (Fin a ⊕ Fin b) T)
    (normalize_eq_of_isCanonical hc)) hR

theorem exists_volumeSchemaUnderlyingIso
    {U V : PositiveRVVolumeObject (M := M) S k}
    {F : GammaRVVolumeSchema B p U.underlying.obj.arity k sp}
    {G : GammaRVVolumeSchema B p V.underlying.obj.arity k sp}
    (P : RVVolumeSchemaRow U F z) (Q : RVVolumeSchemaRow V G z)
    (H : Set (Fin ((p+U.underlying.obj.arity)+V.underlying.obj.arity) → M))
    (hH : DefinableOverBase B
      (Fin.append (Fin.append sp (fun _ : Fin U.underlying.obj.arity => .rv))
        (fun _ : Fin V.underlying.obj.arity => .rv)) H)
    (hBij : bijectiveMapRowValid sp (fun _ => .rv)
      (essentialFiniteVolumeSchema F.object).domain (essentialFiniteVolumeSchema G.object).domain H z)
    (hDef : (rawRVSpace (M := M) U.underlying.obj.arity).RelationDefinable
      (rawRVSpace (M := M) V.underlying.obj.arity) S
      (fun x y => Fin.append (Fin.append z (rvValues x)) (rvValues y) ∈ H)) :
    ∃ e : U.essential ≅ V.essential, ∀ x y, Fin.append (Fin.append z x) y ∈ H ↔
      ∃ u : U.essential.obj.domain, rvValues u.val = x ∧ rvValues (finiteIsoMap e u).val = y := by
  let R (x : Fin U.underlying.obj.arity → CanonicalRV.RVSort M)
      (y : Fin V.underlying.obj.arity → CanonicalRV.RVSort M) :=
    Fin.append (Fin.append z (rvValues x)) (rvValues y) ∈ H
  have hdom (x y) (h : R x y) : x ∈ U.essential.obj.domain.carrier ∧ y ∈ V.essential.obj.domain.carrier :=
    ⟨(P.essential_domain_iff x).mp (hBij.1.2.2.1 _ _ h),
      (Q.essential_domain_iff y).mp ((hBij.2 _).mpr ⟨_,h⟩)⟩
  have htotal (u : U.essential.obj.domain) : ∃ y, R u.val y := by
    obtain ⟨y,hy,_⟩ := hBij.1.2.1 (rvValues u.val) ((P.essential_domain_iff _).mpr u.property)
    have hyRV (i) : iRV (y i) := by
      simpa only [Fin.append_right,sortEval,iRV] using hH.proper _ hy
        (Fin.natAdd (p+U.underlying.obj.arity) i)
    exact ⟨fun i => ⟨y i,hyRV i⟩,hy⟩
  have hunique (x y y') (h : R x y) (h' : R x y') : y = y' := by
    apply rvValues_injective
    exact (hBij.1.2.1 (rvValues x) (hBij.1.2.2.1 _ _ h)).unique h h'
  let f := Map.ofFunctionalRelation hDef hdom htotal hunique
  have hf (u : U.essential.obj.domain) : R u.val (f u).val :=
    Map.ofFunctionalRelation_graph hDef hdom htotal hunique u
  have hfb : Function.Bijective f := by
    constructor
    · intro u u' he
      have hy := (Q.essential_domain_iff (f u).val).mpr (f u).property
      have hu := hBij.unique_reverse (rvValues (f u).val) hy (fun i => (f u).val i |>.property)
      apply Subtype.ext
      apply rvValues_injective
      exact hu.unique (hf u) (he.symm ▸ hf u')
    · intro v
      obtain ⟨x,hx⟩ := (hBij.2 (rvValues v.val)).mp ((Q.essential_domain_iff _).mpr v.property)
      have hxRV (i) : iRV (x i) := by
        simpa only [Fin.append_left,Fin.append_right,sortEval,iRV] using hH.proper _ hx
          (Fin.castAdd V.underlying.obj.arity (Fin.natAdd p i))
      let xt : Fin U.underlying.obj.arity → CanonicalRV.RVSort M := fun i => ⟨x i,hxRV i⟩
      let u : U.essential.obj.domain := ⟨xt,(hdom xt v.val hx).1⟩
      exact ⟨u,Subtype.ext (hunique u.val (f u).val v.val (hf u) hx)⟩
  let e := finiteIsoOfNondegenerateBijection f hfb U.essential_nonzero V.essential_nonzero
  refine ⟨e,?_⟩
  intro x y
  constructor
  · intro hxy
    have hxRV (i) : iRV (x i) := by
      simpa only [Fin.append_left,Fin.append_right,sortEval,iRV] using hH.proper _ hxy
        (Fin.castAdd V.underlying.obj.arity (Fin.natAdd p i))
    have hyRV (i) : iRV (y i) := by
      simpa only [Fin.append_right,sortEval,iRV] using hH.proper _ hxy
        (Fin.natAdd (p+U.underlying.obj.arity) i)
    let xt : Fin U.underlying.obj.arity → CanonicalRV.RVSort M := fun i => ⟨x i,hxRV i⟩
    let yt : Fin V.underlying.obj.arity → CanonicalRV.RVSort M := fun i => ⟨y i,hyRV i⟩
    let u : U.essential.obj.domain := ⟨xt,(hdom xt yt hxy).1⟩
    refine ⟨u,rfl,?_⟩
    exact congrArg rvValues (hunique u.val (f u).val yt (hf u) hxy)
  · rintro ⟨u,rfl,rfl⟩
    exact hf u

end IntegrationInACVF.Section7
