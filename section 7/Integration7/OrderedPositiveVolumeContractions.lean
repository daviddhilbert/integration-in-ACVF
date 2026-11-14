import Integration7.NativeVolumeDomains
import Integration7.RVCoordinateSelection
import Integration7.RVVolumeObjects
import IntegrationSection6.OrderedSelectedVolume

/-! Positive selected-volume objects of actual ordered contractions.
Selected fibre finiteness is proved by the checked Section 6 theorem.
The density is an original retained RV label, as on the density graph;
it is not an assumed comparison or integration value. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a l k : ℕ}

def orderedPositiveVolumeSelector {S : Set M}
    {A : SpecialTransformations.Section5.DefSet (M := M) S n a}
    {U : SpecialTransformations.Section5.DefSet (M := M) S 0 l}
    (T : Section5.OrderedContractionProgram S A U) (ρ : Fin (k + 1) → Fin a) :
    Fin ((n + k) + 1) → Fin l :=
  Section6.orderedSelectedIndex T ρ ∘ (finCongr (Section6.orderedVolumeDegree_eq n (k + 1))).symm

def orderedPositiveVolumeFinite
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M)))
    (A : DefSet (rawMixedSpace (M := M) n a) (C.base : Set M))
    (ρ : Fin (k + 1) → Fin a)
    (hfin : ∀ (x : Fin n → VFType (M := M)) (t : Fin (k + 1) → CanonicalRV.RVSort M),
      {r : Fin a → CanonicalRV.RVSort M | (x, r) ∈ A.carrier ∧ r ∘ ρ = t}.Finite)
    {U : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 l}
    (T : Section5.OrderedContractionProgram (C.base : Set M) (nativeMixedVolumeDomain hc A) U)
    (hT : Section5.GammaProgramDefinable (⟨(C.base : Set M), Ξ⟩ : Base (M := M)) T) :
    RVFiniteObject (M := M) (C.base : Set M) ((n + k) + 1) where
  obj := ⟨l, rawVolumeContractionLabels hc U,
    (rvCoordinateSelectMap (C.base : Set M) (orderedPositiveVolumeSelector T ρ)).restrict
      (Set.subset_univ _)⟩
  property := by
    intro y
    let e := finCongr (Section6.orderedVolumeDegree_eq n (k + 1))
    have hF := Section6.ordered_selected_fibres_finite C.uncountable.le C.saturated C.small T hT ρ hfin
    apply (hF (y.val ∘ e)).of_injOn (f := fun u : rawVolumeContractionLabels hc U => u.val)
    · intro u hu
      refine ⟨(mem_rawVolumeContractionLabels hc U u.val).mp u.property, ?_⟩
      funext i
      have hv := congrArg Subtype.val hu
      have hi := congrFun hv (e i)
      change (u.val ∘ orderedPositiveVolumeSelector T ρ) (e i) = y.val (e i) at hi
      simpa only [orderedPositiveVolumeSelector, Function.comp_apply, e, Equiv.symm_apply_apply] using hi
    · intro u hu v hv he
      exact Subtype.ext he

def orderedPositiveVolumeObject
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M)))
    (A : DefSet (rawMixedSpace (M := M) n a) (C.base : Set M))
    (ω : VolumeForm A) (ρ : Fin (k + 1) → Fin a) (δ : Fin a)
    (hDensity : ∀ p : A, ω.value p = p.val.2 δ)
    (hfin : ∀ (x : Fin n → VFType (M := M)) (t : Fin (k + 1) → CanonicalRV.RVSort M),
      {r : Fin a → CanonicalRV.RVSort M | (x, r) ∈ A.carrier ∧ r ∘ ρ = t}.Finite)
    {U : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 l}
    (T : Section5.OrderedContractionProgram (C.base : Set M) (nativeMixedVolumeDomain hc A) U)
    (hT : Section5.GammaProgramDefinable (⟨(C.base : Set M), Ξ⟩ : Base (M := M)) T) :
    PositiveRVVolumeObject (M := M) (C.base : Set M) (n + k) where
  underlying := orderedPositiveVolumeFinite hc C Ξ A ρ hfin T hT
  form := {
    map := (rvCoordinateSelectMap (C.base : Set M)
      (fun _ : Fin 1 => Section5.suffixIndex T.rvArity_le δ)).restrict (Set.subset_univ _)
    nonzero := by
      intro u
      let q : U := ⟨(Fin.elim0, u.val), (mem_rawVolumeContractionLabels hc U u.val).mp u.property⟩
      obtain ⟨p, hp⟩ := T.surjective q
      have hδ := T.oldLabels p δ
      rw [hp] at hδ
      change u.val (Section5.suffixIndex T.rvArity_le δ) = p.val.2 δ at hδ
      change u.val (Section5.suffixIndex T.rvArity_le δ) ≠ 0
      exact fun hz => ω.nonzero ⟨p.val, p.property⟩
        ((hDensity ⟨p.val, p.property⟩).trans (hδ.symm.trans hz)) }

theorem orderedPositiveVolumeObject_volume
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M)))
    (A : DefSet (rawMixedSpace (M := M) n a) (C.base : Set M))
    (ω : VolumeForm A) (ρ : Fin (k + 1) → Fin a) (δ : Fin a)
    (hDensity : ∀ p : A, ω.value p = p.val.2 δ)
    (hfin : ∀ (x : Fin n → VFType (M := M)) (t : Fin (k + 1) → CanonicalRV.RVSort M),
      {r : Fin a → CanonicalRV.RVSort M | (x, r) ∈ A.carrier ∧ r ∘ ρ = t}.Finite)
    {U : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 l}
    (T : Section5.OrderedContractionProgram (C.base : Set M) (nativeMixedVolumeDomain hc A) U)
    (hT : Section5.GammaProgramDefinable (⟨(C.base : Set M), Ξ⟩ : Base (M := M)) T)
    (u : rawVolumeContractionLabels hc U) :
    (orderedPositiveVolumeObject hc C Ξ A ω ρ δ hDensity hfin T hT).underlying.obj.value u =
      u.val ∘ orderedPositiveVolumeSelector T ρ := rfl

theorem orderedPositiveVolumeObject_density
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M)))
    (A : DefSet (rawMixedSpace (M := M) n a) (C.base : Set M))
    (ω : VolumeForm A) (ρ : Fin (k + 1) → Fin a) (δ : Fin a)
    (hDensity : ∀ p : A, ω.value p = p.val.2 δ)
    (hfin : ∀ (x : Fin n → VFType (M := M)) (t : Fin (k + 1) → CanonicalRV.RVSort M),
      {r : Fin a → CanonicalRV.RVSort M | (x, r) ∈ A.carrier ∧ r ∘ ρ = t}.Finite)
    {U : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 l}
    (T : Section5.OrderedContractionProgram (C.base : Set M) (nativeMixedVolumeDomain hc A) U)
    (hT : Section5.GammaProgramDefinable (⟨(C.base : Set M), Ξ⟩ : Base (M := M)) T)
    (u : rawVolumeContractionLabels hc U) :
    (orderedPositiveVolumeObject hc C Ξ A ω ρ δ hDensity hfin T hT).form.value u =
      u.val (Section5.suffixIndex T.rvArity_le δ) := rfl

end IntegrationInACVF.Section7
