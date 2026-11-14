import Integration7.GammaVolumeIndexedPresentations
import Integration7.GammaVolumePresentationContexts
import Integration7.VolumeSchemaRowSemantics
import Integration7.RVParameterVolumeFibres

/-! The actual fixed-parameter fibres of a joint indexed volume
presentation interpret precisely the original volume-schema rows. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open SpecialTransformations.Section5 (RV)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a d k : ℕ}
variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}
variable {F : GammaRVVolumeSchema B p a k (fun _ => .rv)}
variable {BP : GammaFiniteGraphPresentation B p d T R}

theorem indexedVolume_coordinates (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (P : F.IndexedPresentation BP) (hP : P.finite.codes ⊆ (C.base : Set M))
    (u : (P.inContext hc C hP).underlying.obj.domain) :
    (P.inContext hc C hP).underlying.obj.value u =
      Fin.append (BP.totalVolume (indexedLeft u.val))
        (F.object.rowValue (rvValues (indexedLeft u.val)) (indexedRight u.val)) := by
  have h := ((P.finite.graph_iff u.val ((P.inContext hc C hP).underlying.obj.value u)).mp
    ⟨⟨u.val,u.property⟩,rfl,rfl⟩).2.2
  exact h.symm

theorem indexedVolume_fibre_head (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (P : F.IndexedPresentation BP) (hP : P.finite.codes ⊆ (C.base : Set M))
    (t : Fin p → RV (M := M))
    (u : rvTupleFibre (P.inContext hc C hP).underlying.obj.domain t) :
    ((P.inContext hc C hP).underlying.obj.volume ⟨Fin.append t u.val,u.property⟩).val ∘
      Fin.castAdd (k+1) = BP.totalVolume t := by
  have h := indexedVolume_coordinates hc C P hP ⟨Fin.append t u.val,u.property⟩
  funext i
  have h' := congrFun h (Fin.castAdd (k+1) i)
  simpa only [RVObject.value,Fin.append_left,indexedLeft,Function.comp_def] using h'

def indexedRowVolumeObject (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (P : F.IndexedPresentation BP) (hP : P.finite.codes ⊆ (C.base : Set M))
    (t : Fin p → RV (M := M)) :
    PositiveRVVolumeObject (M := M) ((C.base : Set M) ∪ Set.range (rvValues t)) k :=
  rvTupleVolumeFibre (P.inContext hc C hP).underlying.obj.domain
    (P.inContext hc C hP).underlying.obj.volume (P.inContext hc C hP).underlying.property
    (P.inContext hc C hP).form t (BP.totalVolume t) (indexedVolume_fibre_head hc C P hP t)

theorem indexedRow_schemaRow (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (P : F.IndexedPresentation BP) (hP : P.finite.codes ⊆ (C.base : Set M))
    (t : Fin p → RV (M := M)) (ht : t ∈ T) (hF : F.valid (rvValues t)) :
    RVVolumeSchemaRow (indexedRowVolumeObject hc C P hP t) F (rvValues t) := by
  have hLabel (x : Fin a → RV (M := M)) :
      Fin.append t x ∈ (P.inContext hc C hP).underlying.obj.domain.carrier ↔
        x ∈ F.object.rowDomain (rvValues t) := by
    have h := Set.ext_iff.mp (GammaVolumeGraphPresentation.inContext_domain hc C P hP) (Fin.append t x)
    change (_ ↔ Fin.append t x ∈ indexedDomain T (fun t => F.object.rowDomain (rvValues t))) at h
    simpa only [indexedDomain,Set.mem_ofPred_eq,indexedLeft,indexedRight,Function.comp_def,Fin.append_left,Fin.append_right,
      ht,true_and] using h
  have hCoordinates (u : (indexedRowVolumeObject hc C P hP t).underlying.obj.domain) :
      (indexedRowVolumeObject hc C P hP t).underlying.obj.value u = F.object.rowValue (rvValues t) u.val := by
    have h := indexedVolume_coordinates hc C P hP ⟨Fin.append t u.val,u.property⟩
    funext i
    have h' := congrFun h (Fin.natAdd d i)
    simpa only [indexedRowVolumeObject,rvTupleVolumeFibre,RVObject.value,rvTupleFibreVolumeMap_value,
      Function.comp_apply,indexedLeft,indexedRight,Function.comp_def,Fin.append_left,Fin.append_right] using h'
  constructor
  · intro x v
    constructor
    · intro hv
      have hx := hF.1.2.2.1 _ _ hv
      refine ⟨⟨x,(hLabel x).mpr hx⟩,rfl,?_⟩
      exact (hCoordinates _).trans ((F.object.rowValue_graph _ hF.1 x hx v).mp hv)
    · rintro ⟨u,rfl,hv⟩
      exact (F.object.rowValue_graph _ hF.1 u.val ((hLabel _).mp u.property) v).mpr
        ((hCoordinates u).symm.trans hv)
  · intro x ω
    constructor
    · intro hω
      have hx := F.rowDensity_support _ hF x ω hω
      let u : (indexedRowVolumeObject hc C P hP t).underlying.obj.domain := ⟨x,(hLabel x).mpr hx⟩
      have hρ : F.indexedDensity T (Fin.append t x) ω := by
        refine ⟨?_,?_⟩
        · simpa only [indexedDomain,Set.mem_ofPred_eq,indexedLeft,indexedRight,Function.comp_def,Fin.append_left,Fin.append_right]
            using And.intro ht hx
        · simpa only [indexedLeft,indexedRight,Function.comp_def,Fin.append_left,Fin.append_right] using hω
      obtain ⟨v,hv,hvω⟩ := (P.canonicalData_density_iff hc (Fin.append t x) ω).mpr hρ
      have he : v = (⟨Fin.append t x,u.property⟩ : (P.canonicalData hc).underlying.obj.domain) := Subtype.ext hv
      refine ⟨u,rfl,?_⟩
      change ((P.canonicalData hc).form.map ⟨Fin.append t x,u.property⟩).val = ω
      exact (congrArg (fun v => ((P.canonicalData hc).form.map v).val) he).symm.trans hvω
    · rintro ⟨u,rfl,hω⟩
      have hρ := (P.canonicalData_density_iff hc (Fin.append t u.val) ω).mp
        ⟨⟨Fin.append t u.val,u.property⟩,rfl,hω⟩
      simpa only [indexedLeft,indexedRight,Function.comp_def,Fin.append_left,Fin.append_right] using hρ.2

end IntegrationInACVF.Section7
