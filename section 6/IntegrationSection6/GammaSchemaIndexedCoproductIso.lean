import IntegrationSection6.GammaSchemaIndexedPresentations
import IntegrationSection6.GammaIndexedCoproductGraphs
import IntegrationSection6.IndexedCoproductVolumes
import IntegrationSection6.GammaGraphCoproductValues

/-! Indexed assembly commutes with the actual native finite coproduct,
by an original-Gamma isomorphism preserving the full volume tuple. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b d k : ℕ}
variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

def GammaFiniteRVSchema.indexedCoprodIso
    (F : GammaFiniteRVSchema B p a k (fun _ => .rv))
    (G : GammaFiniteRVSchema B p b k (fun _ => .rv)) (BP : GammaFiniteGraphPresentation B p d T R)
    (hF : ∀ t ∈ T, F.finiteRow (fun j => (t j).val))
    (hG : ∀ t ∈ T, G.finiteRow (fun j => (t j).val))
    (P : F.IndexedPresentation BP) (Q : G.IndexedPresentation BP) (Z : F.IndexedCoprodPresentation G BP) :
    GammaRVIso Z.toGamma.toGammaRVObject (P.coprod Q).toGamma.toGammaRVObject := by
  let D := fun t : Fin p → RV (M := M) => F.rowDomain (fun j => (t j).val)
  let E := fun t : Fin p → RV (M := M) => G.rowDomain (fun j => (t j).val)
  let C := P.coprod Q
  let e := Z.domainEquiv.trans ((indexedCoprodEquiv T D E).trans C.domainEquiv.symm)
  refine FiniteRV.gammaIsoOfFiniteEquiv Z.toGamma C.toGamma e ?_ ?_
  · apply GammaGraphDefinable.congr
      (gamma_indexed_coprod_equiv_graph T D E (F.indexed_domain_graph BP) (G.indexed_domain_graph BP))
    intro w y
    constructor
    · rintro ⟨u,hu,hy⟩
      exact ⟨Z.domainEquiv.symm u,hu,hy⟩
    · rintro ⟨u,hu,hy⟩
      exact ⟨Z.domainEquiv u,hu,hy⟩
  · intro u
    change rawWeight (fun j => ((Z.volume u).val j).val) = rawWeight (fun j => ((C.volume (e u)).val j).val)
    apply congrArg (fun v : Fin (d+k) → RV (M := M) => rawWeight (fun j => (v j).val))
    have hZ : (Z.volume u).val =
        indexedVolume BP.totalVolume (fun t => (F.coprodFormula G).rowValue (fun j => (t j).val)) u.val :=
      ((Z.graph_iff u.val (Z.volume u).val).mp ⟨u,rfl,rfl⟩).2.2.symm
    rcases indexedCoprod_cases T D E (Z.domainEquiv u) with ⟨t,x,he⟩ | ⟨t,x,he⟩
    · let px : P.domain := P.domainEquiv.symm ((indexedSigmaEquiv T D).symm ⟨t,x⟩)
      have hu : u.val = (indexedCoprodLeft T D E t x).val := congrArg Subtype.val he
      have hImage : (e u).val = @rvLeftTag M N hN (p+a) (p+b) (Fin.append t.val x.val) := by
        change (indexedCoprodEquiv T D E (Z.domainEquiv u)).val = _
        rw [he]
        exact indexedCoprodEquiv_left T D E t x
      have hTarget := P.coprod_value_at_left Q px (e u) hImage
      calc
        (Z.volume u).val = indexedVolume BP.totalVolume
            (fun t => (F.coprodFormula G).rowValue (fun j => (t j).val)) u.val := hZ
        _ = indexedVolume BP.totalVolume
            (fun t => (F.coprodFormula G).rowValue (fun j => (t j).val)) (indexedCoprodLeft T D E t x).val :=
          congrArg _ hu
        _ = indexedVolume BP.totalVolume (fun t => F.rowValue (fun j => (t j).val)) px.val :=
          indexedCoprodLeft_volume F G T BP.totalVolume t x (hF t.val t.property) (hG t.val t.property)
        _ = (P.volume px).val := ((P.graph_iff px.val (P.volume px).val).mp ⟨px,rfl,rfl⟩).2.2
        _ = (C.volume (e u)).val := hTarget.symm
    · let px : Q.domain := Q.domainEquiv.symm ((indexedSigmaEquiv T E).symm ⟨t,x⟩)
      have hu : u.val = (indexedCoprodRight T D E t x).val := congrArg Subtype.val he
      have hImage : (e u).val = @rvRightTag M N hN (p+b) (p+a) (Fin.append t.val x.val) := by
        change (indexedCoprodEquiv T D E (Z.domainEquiv u)).val = _
        rw [he]
        exact indexedCoprodEquiv_right T D E t x
      have hTarget := P.coprod_value_at_right Q px (e u) hImage
      calc
        (Z.volume u).val = indexedVolume BP.totalVolume
            (fun t => (F.coprodFormula G).rowValue (fun j => (t j).val)) u.val := hZ
        _ = indexedVolume BP.totalVolume
            (fun t => (F.coprodFormula G).rowValue (fun j => (t j).val)) (indexedCoprodRight T D E t x).val :=
          congrArg _ hu
        _ = indexedVolume BP.totalVolume (fun t => G.rowValue (fun j => (t j).val)) px.val :=
          indexedCoprodRight_volume F G T BP.totalVolume t x (hF t.val t.property) (hG t.val t.property)
        _ = (Q.volume px).val := ((Q.graph_iff px.val (Q.volume px).val).mp ⟨px,rfl,rfl⟩).2.2
        _ = (C.volume (e u)).val := hTarget.symm

end IntegrationInACVF.Section6
