import Integration7.VolumeSchemaValiditySemantics

/-! The first-order Gamma clause gives the actual density-weighted
absolute product equality at each pair in the certificate chart. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open scoped BigOperators

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem rvValues_finAppend {n m : ℕ} (u : Fin n → CanonicalRV.RVSort M) (v : Fin m → CanonicalRV.RVSort M) :
    rvValues (Fin.append u v) = Fin.append (rvValues u) (rvValues v) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp only [rvValues,Fin.append_left,Fin.append_right]

theorem volumeChartGammaRowValid.absolute_weight {B : Base (M := M)} {p a b k : ℕ} {sp : Fin p → SortTag}
    (F : GammaRVVolumeSchema B p a k sp) (G : GammaRVVolumeSchema B p b k sp)
    (H : Set (Fin ((p+a)+b) → M)) (z : Fin p → M) (hΓ : volumeChartGammaRowValid F G H z)
    (x : Fin a → CanonicalRV.RVSort M) (y : Fin b → CanonicalRV.RVSort M)
    (u v : Fin (k+1) → CanonicalRV.RVSort M) (φ ψ : CanonicalRV.RVSort M)
    (hU : F.object.rowVolume z x u) (hV : G.object.rowVolume z y v)
    (hφ : F.rowDensity z x (fun _ => φ)) (hψ : G.rowDensity z y (fun _ => ψ))
    (hChart : Fin.append (Fin.append z (rvValues x)) (rvValues y) ∈ H) :
    RVOperations.absoluteHom φ * (∏ i, RVOperations.absoluteHom (u i)) =
      RVOperations.absoluteHom ψ * (∏ i, RVOperations.absoluteHom (v i)) := by
  let wU := Fin.append u (fun _ : Fin 1 => φ)
  let wV := Fin.append v (fun _ : Fin 1 => ψ)
  have hWU : Fin.append (Fin.append z (rvValues x)) (rvValues wU) ∈ weightedVolumeGraph F := by
    rw [show rvValues wU = Fin.append (rvValues u) (fun _ : Fin 1 => φ.val) from rvValues_finAppend u _]
    exact (weightedVolumeGraph_append F z _ _ _).mpr ⟨hU,hφ⟩
  have hWV : Fin.append (Fin.append z (rvValues y)) (rvValues wV) ∈ weightedVolumeGraph G := by
    rw [show rvValues wV = Fin.append (rvValues v) (fun _ : Fin 1 => ψ.val) from rvValues_finAppend v _]
    exact (weightedVolumeGraph_append G z _ _ _).mpr ⟨hV,hψ⟩
  have hBalance := volumeChartGammaRowValid_apply F G H z hΓ (rvValues wU) (rvValues wV)
    (fun i => (wU i).property) (fun i => (wV i).property) (rvValues x) (rvValues y) hWU hChart hWV
  have hVal := ((rvProductGammaBalance_append ((k+1)+1) wU wV).mp hBalance).2.2
  have hAbs := congrArg paperAbsoluteHom hVal
  change RVOperations.absoluteHom (∏ i, wU i) = RVOperations.absoluteHom (∏ i, wV i) at hAbs
  have hProdU : (∏ i, wU i) = (∏ i, u i) * φ := by
    rw [show (∏ i, wU i) = _ from Fin.prod_univ_add (fun i => wU i)]
    simp only [wU,Fin.append_left,Fin.append_right,Fin.prod_univ_one]
  have hProdV : (∏ i, wV i) = (∏ i, v i) * ψ := by
    rw [show (∏ i, wV i) = _ from Fin.prod_univ_add (fun i => wV i)]
    simp only [wV,Fin.append_left,Fin.append_right,Fin.prod_univ_one]
  rw [hProdU,hProdV,map_mul,map_mul,map_prod,map_prod] at hAbs
  exact (mul_comm _ _).trans (hAbs.trans (mul_comm _ _))

end IntegrationInACVF.Section7
