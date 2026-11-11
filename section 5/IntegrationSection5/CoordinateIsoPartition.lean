import IntegrationSection5.CoordinatePartitionAt
import IntegrationSection5.GammaUnaryChain

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
open IntegrationInACVF.Section4
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {p m u w : ℕ}
variable {A : Set (Point (M := M) (p+1) m)} {B : Set (Point (M := M) u w)}

theorem coordinate_injective_iso_partition {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk G.real < κ)
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ) (hu : 0 < u)
    (e : GammaIso G A B) (i : Fin (p+1)) : Nonempty (CoordinateRVPartition G i e.equiv) := by
  have hA := (e.symm (gammaLogicInput G)).target_definable (gammaLogicInput G)
  have hB := e.target_definable (gammaLogicInput G)
  obtain ⟨S,_,hAr,hBr,her⟩ := common_gamma_presentation A B e.equiv hA hB e.graph
  let AR : DefSet (M := M) S (p+1) m := @PresentedSet.mk M sM (pointSpace (p+1) m) S A hAr
  let BR : DefSet (M := M) S u w := @PresentedSet.mk M sM (pointSpace u w) S B hBr
  let f : Map AR BR := @Map.mk M sM (pointSpace (p+1) m) (pointSpace u w) S AR BR e.equiv her
  exact coordinate_injective_partition_at hκ hs h00 G hsmall δ hδ AR hA hu f e.equiv.bijective e.graph i

variable {B' : Set (Point (M := M) (p+1) w)}

theorem CoordinateRVPartition.active_coordinate {i : Fin (p+1)} {f : A → B'}
    (P : CoordinateRVPartition G i f) (F : Finset (Fin (p+1))) (hi : i ∈ F)
    (hfix : ∀ a : A, ∀ j : Fin (p+1), j ∉ F → (f a).val.1 j = a.val.1 j)
    (k : Option (Fin (p+1))) :
    ∃ j : Fin (p+1), j ∈ F ∧ ∀ a b : A, a.val ∈ P.pieces k → b.val ∈ P.pieces k →
      SameCoordinateContext i a.val b.val → P.code.toFun a = P.code.toFun b →
        vfAt (f a).val j = vfAt (f b).val j → a = b := by
  by_cases hj : P.coordinate k ∈ F
  · exact ⟨P.coordinate k,hj,P.injective k⟩
  · refine ⟨i,hi,?_⟩
    intro a b ha hb hctx hcode _
    apply P.injective k a b ha hb hctx hcode
    have hji : P.coordinate k ≠ i := fun he => hj (he.symm ▸ hi)
    exact (hfix a _ hj).trans ((hctx.1 _ hji).trans (hfix b _ hj).symm)

end IntegrationInACVF.Section5
