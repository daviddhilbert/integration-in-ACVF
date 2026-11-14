import Integration7.VolumeForms
import Integration7.RVCoordinateSelection

/-! Specialization at an actual RV parameter tuple retains the original
fibre labels and pulls back the density along literal tuple insertion. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p a : ℕ}

def rvInsertHeadMap (S : Set M) (t : Fin p → CanonicalRV.RVSort M) (a : ℕ) :
    Map (DefSet.univ (rawRVSpace (M := M) a) (S ∪ Set.range (rvValues t)))
      (DefSet.univ (rawRVSpace (M := M) (p+a)) (S ∪ Set.range (rvValues t))) := by
  let F (z : Fin a → M) := Fin.append (rvValues t) z
  have hF : (S ∪ Set.range (rvValues t)).DefinableMap LRV F := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · have h : (S ∪ Set.range (rvValues t)).DefinableFun LRV
          (fun _ : Fin a → M => rvValues t i) :=
        LRV.definableFun_const (Fin a) (Or.inr (Set.mem_range_self i))
      simpa only [F,Fin.append_left] using h
    · simpa only [F,Fin.append_right] using (Set.DefinableFun.proj (L := LRV) (i := i))
  have hcode (c : (rawRVSpace (M := M) a).domain) :
      rvValues (Fin.append t ((rawRVSpace a).decode c)) = F c.val := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [rvValues,F,Fin.append_left]
    · simpa only [rvValues,F,Fin.append_right] using congrFun (rvValues_decode c) i
  refine Map.ofCodes _ (fun r => Fin.append t r) F hF
    (fun c => ⟨Fin.append t ((rawRVSpace a).decode c),hcode c⟩) ?_
  intro c
  exact rvValues_injective ((rvValues_decode _).trans (hcode c).symm)

def rvTupleFibre (A : DefSet (rawRVSpace (M := M) (p+a)) S) (t : Fin p → CanonicalRV.RVSort M) :
    DefSet (rawRVSpace (M := M) a) (S ∪ Set.range (rvValues t)) where
  carrier := {r | Fin.append t r ∈ A.carrier}
  definable := by
    have h := (rvInsertHeadMap S t a).definable_preimage (A.definable.mono _ Set.subset_union_left)
    convert h using 1
    ext r
    constructor
    · intro hr
      exact ⟨⟨r,Set.mem_univ _⟩,rfl,hr⟩
    · rintro ⟨r',rfl,hr⟩
      exact hr

def rvTupleFibreEmbed (A : DefSet (rawRVSpace (M := M) (p+a)) S) (t : Fin p → CanonicalRV.RVSort M) :
    Map (rvTupleFibre A t) (A.extend (Set.subset_union_left : S ⊆ S ∪ Set.range (rvValues t))) where
  toFun r := ⟨Fin.append t r.val,r.property⟩
  graph_definable := ((rvInsertHeadMap S t a).restrict
    (A' := rvTupleFibre A t) (Set.subset_univ _)).graph_definable

def VolumeForm.rvTupleFibre {A : DefSet (rawRVSpace (M := M) (p+a)) S}
    (ω : VolumeForm A) (t : Fin p → CanonicalRV.RVSort M) : VolumeForm (rvTupleFibre A t) :=
  (ω.extend Set.subset_union_left).pullback (rvTupleFibreEmbed A t)

@[simp] theorem VolumeForm.rvTupleFibre_value {A : DefSet (rawRVSpace (M := M) (p+a)) S}
    (ω : VolumeForm A) (t : Fin p → CanonicalRV.RVSort M) (r : IntegrationInACVF.Section7.rvTupleFibre A t) :
    (ω.rvTupleFibre t).value r = ω.value ⟨Fin.append t r.val,r.property⟩ := rfl

end IntegrationInACVF.Section7
