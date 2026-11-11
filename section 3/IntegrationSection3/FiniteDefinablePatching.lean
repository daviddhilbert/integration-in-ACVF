module

public import IntegrationSection3.ACFDefinableInjection

@[expose] public section

/-! Finite tuples and finite patches are definable after naming their
coordinates. This purely logical lemma uses the full universe as an
intermediate real parameter base; no new parameter occurs in a counting
conclusion. -/

open Set Classical FirstOrder FirstOrder.Language

namespace IntegrationInACVF.Section3.FiniteDefinablePatching

theorem singleton_univ {K ι : Type*} (L : Language) [L.Structure K] [Finite ι]
    (w : ι → K) : (Set.univ : Set K).Definable L {w} := by
  have hd := Set.definable_iInter_of_finite (fun i : ι =>
    (@Set.DefinableFun.proj K L _ ι Set.univ i).ofPred_eq
      (L.definableFun_const ι (Set.mem_univ (w i))))
  convert hd using 1
  ext z
  simp only [Set.mem_singleton_iff,Set.mem_iInter,Set.mem_ofPred_eq]
  exact funext_iff

theorem finite_univ {K ι : Type*} (L : Language) [L.Structure K] [Finite ι]
    {R : Set (ι → K)} (hR : R.Finite) : (Set.univ : Set K).Definable L R := by
  letI := hR.fintype
  have hd := Set.definable_iUnion_of_finite (fun w : R => singleton_univ L w.val)
  convert hd using 1
  ext z
  simp only [Set.mem_iUnion,Set.mem_singleton_iff]
  exact ⟨fun h => ⟨⟨z,h⟩,rfl⟩,fun ⟨w,he⟩ => he.symm ▸ w.property⟩

end IntegrationInACVF.Section3.FiniteDefinablePatching
