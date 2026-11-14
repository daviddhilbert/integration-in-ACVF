import Integration7.VolumeCoordinatePermutation
import Integration7.VolumeDegreeTransport
import Integration7.VolumeProductPointwise
import Integration7.PermutationSignParameters
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section9 SpecialTransformations.DefinableGeometry
noncomputable section
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n m : ℕ}

theorem positiveProduct_degree_swap (n m : ℕ) : (n+1)+m = (m+1)+n := by omega

def positiveProductSwapPermutation (n m : ℕ) : Equiv.Perm (Fin (((n+1)+m)+1)) :=
  (finCongr (congrArg Nat.succ (positiveProduct_degree_swap n m))).trans
    (finAddFlip : Fin ((m+1)+(n+1)) ≃ Fin ((n+1)+(m+1)))

def positiveProductSwapSign (n m : ℕ) : CanonicalRV.RVSort M :=
  rvPermutationSign (positiveProductSwapPermutation n m)

def signedProductSwapObject (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) n)
    (V : PositiveRVVolumeObject (M := M) (C.base : Set M) m) :
    PositiveRVVolumeObject (M := M) (C.base : Set M) ((n+1)+m) :=
  ((V.prod U).reindexDegree (positiveProduct_degree_swap n m)).rescale
    (positiveProductSwapSign (M := M) n m)⁻¹
    (SpecialTransformations.Section4.ResiduePurity.rv_inv_mem_base C.base (rvPermutationSign_mem C.base _))
    (inv_ne_zero (rvPermutationSign_ne_zero _))

theorem rvProductSwapMap_pair {S : Set M} {a b : ℕ}
    (U : RVObject (M := M) S a) (V : RVObject (M := M) S b) (u : U.domain) (v : V.domain) :
    rvProductSwapMap U V (rvPackPair U.domain V.domain u v) = rvPackPair V.domain U.domain v u := by
  simp only [rvProductSwapMap, Map.comp_apply, rvUnpack_pair]
  rfl

theorem signedProductSwap_coordinates (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) n)
    (V : PositiveRVVolumeObject (M := M) (C.base : Set M) m)
    (w : (U.prod V).underlying.obj.domain) :
    (signedProductSwapObject C U V).underlying.obj.value
      (rvProductSwapMap U.underlying.obj V.underlying.obj w) =
      (U.prod V).underlying.obj.value w ∘ positiveProductSwapPermutation n m := by
  obtain ⟨u, v, rfl⟩ := exists_rvPackPair U.underlying.obj.domain V.underlying.obj.domain w
  rw [rvProductSwapMap_pair]
  change (rvProductObject V.underlying.obj U.underlying.obj).value
      (rvPackPair V.underlying.obj.domain U.underlying.obj.domain v u) ∘
        finCongr (congrArg Nat.succ (positiveProduct_degree_swap n m)) =
    (rvProductObject U.underlying.obj V.underlying.obj).value
      (rvPackPair U.underlying.obj.domain V.underlying.obj.domain u v) ∘ positiveProductSwapPermutation n m
  rw [rvProductObject_value_pair, rvProductObject_value_pair]
  funext i
  exact (congrFun (rvAppend_flip (V.underlying.obj.value v) (U.underlying.obj.value u))
    ((finCongr (congrArg Nat.succ (positiveProduct_degree_swap n m))) i)).symm

theorem signedProductSwap_density (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) n)
    (V : PositiveRVVolumeObject (M := M) (C.base : Set M) m)
    (w : (U.prod V).underlying.obj.domain) :
    (signedProductSwapObject C U V).form.value (rvProductSwapMap U.underlying.obj V.underlying.obj w) =
      (positiveProductSwapSign (M := M) n m)⁻¹ * (U.prod V).form.value w := by
  obtain ⟨u, v, rfl⟩ := exists_rvPackPair U.underlying.obj.domain V.underlying.obj.domain w
  rw [rvProductSwapMap_pair]
  change (positiveProductSwapSign (M := M) n m)⁻¹ * (V.prod U).form.value
      (rvPackPair V.underlying.obj.domain U.underlying.obj.domain v u) = _
  rw [positiveProduct_density_pair V U v u, positiveProduct_density_pair U V u v, mul_comm (V.form.value v)]

def volumeSignedProductSwapIso (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) n)
    (V : PositiveRVVolumeObject (M := M) (C.base : Set M) m) :
    RVVolumeIso (U.prod V) (signedProductSwapObject C U V) := by
  let f : (U.prod V).underlying ≅ (signedProductSwapObject C U V).underlying :=
    rvFiniteIsoOfAmbient (rvIsoOfLabelEquiv
      (U := (U.prod V).underlying.obj) (V := (signedProductSwapObject C U V).underlying.obj)
      (rvProductSwapMap U.underlying.obj V.underlying.obj)
      (rvProductSwapMap_bijective U.underlying.obj V.underlying.obj)
      (rvReindexEquiv (positiveProductSwapPermutation n m))
      (rvWeight_reindex (positiveProductSwapPermutation n m)) (signedProductSwap_coordinates C U V))
  exact RVVolumeIso.of_permuted_coordinates_full hc C f (positiveProductSwapPermutation n m)
    (signedProductSwap_coordinates C U V) (signedProductSwap_density C U V)
end IntegrationInACVF.Section7
