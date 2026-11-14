import Integration7.IndexedVolumeCoproductLabels
import Integration7.IndexedVolumeGammaCompatibility

/-! The density graph survives coproduct/index interchange on each
canonical summand. These are graph identities, with no Jacobian premise. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open SpecialTransformations.Section5 (RV)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b d k : ℕ}
variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem indexedVolume_density_eq {F : GammaRVVolumeSchema B p a k (fun _ => .rv)}
    {BP : GammaFiniteGraphPresentation B p d T R}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (P : F.IndexedPresentation BP) (hP : P.finite.codes ⊆ (C.base : Set M))
    (u : (P.inContext hc C hP).underlying.obj.domain) (ω : Fin 1 → RV (M := M))
    (hω : F.indexedDensity T u.val ω) : ω 0 = (P.inContext hc C hP).form.value u := by
  obtain ⟨v,hv,hρ⟩ := (P.canonicalData_density_iff hc u.val ω).mpr hω
  have he : v = (⟨u.val,u.property⟩ : (P.canonicalData hc).underlying.obj.domain) := Subtype.ext hv
  subst v
  exact (congrFun hρ 0).symm

theorem indexedCoprodLeft_density
    (F : GammaRVVolumeSchema B p a k (fun _ => .rv))
    (G : GammaRVVolumeSchema B p b k (fun _ => .rv))
    (t : Fin p → RV (M := M)) (x : Fin a → RV (M := M)) (ω : Fin 1 → RV (M := M))
    (h : F.indexedDensity T (Fin.append t x) ω) :
    (F.coprodFormula G).indexedDensity T (Fin.append t (@rvLeftTag M N hN a b x)) ω := by
  have h' : (t ∈ T ∧ x ∈ F.object.rowDomain (rvValues t)) ∧ F.rowDensity (rvValues t) x ω := by
    simpa only [GammaRVVolumeSchema.indexedDensity,indexedDomain,Set.mem_ofPred_eq,indexedLeft,indexedRight,
      Function.comp_def,Fin.append_left,Fin.append_right] using h
  have hD := (F.object.coprod_row_domain_formula G.object (rvValues t) (fun i => (t i).property)
    (@rvLeftTag M N hN a b x)).mpr (Or.inl ⟨x,h'.1.2,rfl⟩)
  have hρ := (F.coprod_rowDensity G (rvValues t) (fun i => (t i).property)
    (@rvLeftTag M N hN a b x) ω).mpr (Or.inl ⟨x,h'.2,rfl⟩)
  simp only [GammaRVVolumeSchema.indexedDensity,indexedDomain,Set.mem_ofPred_eq,indexedLeft,indexedRight,
    Function.comp_def,Fin.append_left,Fin.append_right]
  exact ⟨⟨h'.1.1,hD⟩,hρ⟩

theorem indexedCoprodRight_density
    (F : GammaRVVolumeSchema B p a k (fun _ => .rv))
    (G : GammaRVVolumeSchema B p b k (fun _ => .rv))
    (t : Fin p → RV (M := M)) (x : Fin b → RV (M := M)) (ω : Fin 1 → RV (M := M))
    (h : G.indexedDensity T (Fin.append t x) ω) :
    (F.coprodFormula G).indexedDensity T (Fin.append t (@rvRightTag M N hN b a x)) ω := by
  have h' : (t ∈ T ∧ x ∈ G.object.rowDomain (rvValues t)) ∧ G.rowDensity (rvValues t) x ω := by
    simpa only [GammaRVVolumeSchema.indexedDensity,indexedDomain,Set.mem_ofPred_eq,indexedLeft,indexedRight,
      Function.comp_def,Fin.append_left,Fin.append_right] using h
  have hD := (F.object.coprod_row_domain_formula G.object (rvValues t) (fun i => (t i).property)
    (@rvRightTag M N hN b a x)).mpr (Or.inr ⟨x,h'.1.2,rfl⟩)
  have hρ := (F.coprod_rowDensity G (rvValues t) (fun i => (t i).property)
    (@rvRightTag M N hN b a x) ω).mpr (Or.inr ⟨x,h'.2,rfl⟩)
  simp only [GammaRVVolumeSchema.indexedDensity,indexedDomain,Set.mem_ofPred_eq,indexedLeft,indexedRight,
    Function.comp_def,Fin.append_left,Fin.append_right]
  exact ⟨⟨h'.1.1,hD⟩,hρ⟩

end IntegrationInACVF.Section7
