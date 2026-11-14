import Integration7.RVParameterFibres
import Integration7.RVVolumeObjects

/-! A finite joint volume map gives a finite tail-volume map on each
fixed parameter fibre whenever its head volume is fixed on that fibre. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {p a d k : ℕ}

def rvTupleFibreVolumeMap (A : DefSet (rawRVSpace (M := M) (p+a)) S)
    (f : Map A (DefSet.univ (rawRVSpace (M := M) (d+(k+1))) S))
    (t : Fin p → CanonicalRV.RVSort M) :
    Map (rvTupleFibre A t) (DefSet.univ (rawRVSpace (M := M) (k+1)) (S ∪ Set.range (rvValues t))) :=
  (rvCoordinateSelectMap _ (Fin.natAdd d)).comp
    ((f.extend Set.subset_union_left).comp (rvTupleFibreEmbed A t))

@[simp] theorem rvTupleFibreVolumeMap_value (A : DefSet (rawRVSpace (M := M) (p+a)) S)
    (f : Map A (DefSet.univ (rawRVSpace (M := M) (d+(k+1))) S))
    (t : Fin p → CanonicalRV.RVSort M) (u : rvTupleFibre A t) :
    (rvTupleFibreVolumeMap A f t u).val = (f ⟨Fin.append t u.val,u.property⟩).val ∘ Fin.natAdd d := rfl

theorem rvTupleFibreVolumeMap_finite (A : DefSet (rawRVSpace (M := M) (p+a)) S)
    (f : Map A (DefSet.univ (rawRVSpace (M := M) (d+(k+1))) S)) (hf : f.FiniteFibres)
    (t : Fin p → CanonicalRV.RVSort M) (c : Fin d → CanonicalRV.RVSort M)
    (hHead : ∀ u : rvTupleFibre A t, (f ⟨Fin.append t u.val,u.property⟩).val ∘ Fin.castAdd (k+1) = c) :
    (rvTupleFibreVolumeMap A f t).FiniteFibres := by
  intro y
  apply (hf ⟨Fin.append c y.val,Set.mem_univ _⟩).of_injOn
    (f := fun u : rvTupleFibre A t => (⟨Fin.append t u.val,u.property⟩ : A))
  · intro u hu
    apply Subtype.ext
    have hTail : (f ⟨Fin.append t u.val,u.property⟩).val ∘ Fin.natAdd d = y.val :=
      congrArg Subtype.val hu
    exact (Fin.append_castAdd_natAdd (f := (f ⟨Fin.append t u.val,u.property⟩).val)).symm.trans
      (congrArg₂ Fin.append (hHead u) hTail)
  · intro u hu v hv h
    apply Subtype.ext
    funext i
    have he := congrFun (congrArg (fun w : A => w.val) h) (Fin.natAdd p i)
    simpa only [Fin.append_right] using he

def rvTupleVolumeFibre (A : DefSet (rawRVSpace (M := M) (p+a)) S)
    (f : Map A (DefSet.univ (rawRVSpace (M := M) (d+(k+1))) S)) (hf : f.FiniteFibres)
    (ω : VolumeForm A) (t : Fin p → CanonicalRV.RVSort M) (c : Fin d → CanonicalRV.RVSort M)
    (hHead : ∀ u : rvTupleFibre A t, (f ⟨Fin.append t u.val,u.property⟩).val ∘ Fin.castAdd (k+1) = c) :
    PositiveRVVolumeObject (M := M) (S ∪ Set.range (rvValues t)) k where
  underlying := ⟨⟨a,rvTupleFibre A t,rvTupleFibreVolumeMap A f t⟩,
    rvTupleFibreVolumeMap_finite A f hf t c hHead⟩
  form := ω.rvTupleFibre t

end IntegrationInACVF.Section7
