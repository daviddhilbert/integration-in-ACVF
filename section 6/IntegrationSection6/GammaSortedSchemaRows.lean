import IntegrationSection6.GammaFiniteObjectPromotion
import IntegrationSection6.GammaTupleRelationSpecialization

/-! Raw and typed rows for arbitrary sorted parameter tuples. Rebounding
keeps the global formulas, and actual finite row presentations supply a
valid bound by genuine compactness over the original base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a k : ℕ} {sp : Fin p → SortTag}

def GammaFiniteRVSchema.withBound (F : GammaFiniteRVSchema B p a k sp) (bound : ℕ) :
    GammaFiniteRVSchema B p a k sp := { F with bound := bound }

theorem GammaFiniteRVSchema.raw_row_domain_iff (F : GammaFiniteRVSchema B p a k sp)
    (z : Fin p → M) (x : Fin a → M) :
    Fin.append z x ∈ F.domain ↔
      ∃ t : Fin a → RV (M := M), t ∈ F.rowDomain z ∧ (fun j => (t j).val) = x := by
  constructor
  · intro hx
    have hxs (j : Fin a) : iRV (x j) := by
      simpa only [Fin.append_right,sortEval,iRV] using F.domain_definable.proper _ hx (Fin.natAdd p j)
    exact ⟨fun j => ⟨x j,hxs j⟩,hx,rfl⟩
  · rintro ⟨t,ht,rfl⟩
    exact ht

theorem GammaFiniteRVSchema.raw_row_volume_iff (F : GammaFiniteRVSchema B p a k sp)
    (z : Fin p → M) (x : Fin a → M) (y : Fin k → M) :
    Fin.append (Fin.append z x) y ∈ F.volume ↔
      ∃ t : Fin a → RV (M := M), ∃ s : Fin k → RV (M := M),
        F.rowVolume z t s ∧ (fun j => (t j).val) = x ∧ (fun j => (s j).val) = y := by
  constructor
  · intro hxy
    have hxs (j : Fin a) : iRV (x j) := by
      simpa only [Fin.append_left,Fin.append_right,sortEval,iRV] using
        F.volume_definable.proper _ hxy (Fin.castAdd k (Fin.natAdd p j))
    have hys (j : Fin k) : iRV (y j) := by
      simpa only [Fin.append_right,sortEval,iRV] using F.volume_definable.proper _ hxy (Fin.natAdd (p+a) j)
    exact ⟨fun j => ⟨x j,hxs j⟩,fun j => ⟨y j,hys j⟩,hxy,rfl,rfl⟩
  · rintro ⟨t,s,ht,rfl,rfl⟩
    exact ht

theorem GammaFiniteRVSchema.raw_row_domain_presented (F : GammaFiniteRVSchema B p a k sp)
    (z : Fin p → M)
    (P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ a k
      (F.rowDomain z) (F.rowVolume z)) (x : Fin a → M) :
    Fin.append z x ∈ F.domain ↔ x ∈ gammaRawObjectDomain P.toGamma.toGammaRVObject := by
  rw [F.raw_row_domain_iff]
  constructor
  · rintro ⟨t,ht,hx⟩
    exact ⟨⟨t,(Set.ext_iff.mp P.domain_eq t).mpr ht⟩,hx⟩
  · rintro ⟨u,hu⟩
    exact ⟨u.val,((P.graph_iff u.val (P.volume u).val).mp ⟨u,rfl,rfl⟩).1,hu⟩

theorem GammaFiniteRVSchema.raw_row_volume_presented (F : GammaFiniteRVSchema B p a k sp)
    (z : Fin p → M) (hsupport : ∀ t s, F.rowVolume z t s → t ∈ F.rowDomain z)
    (P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ a k
      (F.rowDomain z) (F.rowVolume z)) (x : Fin a → M) (y : Fin k → M) :
    Fin.append (Fin.append z x) y ∈ F.volume ↔
      Fin.append x y ∈ gammaRawObjectVolume P.toGamma.toGammaRVObject := by
  rw [F.raw_row_volume_iff,gammaRawObjectVolume_append_iff]
  constructor
  · rintro ⟨t,s,hv,hx,hy⟩
    obtain ⟨u,hu,hs⟩ := (P.graph_iff t s).mpr ⟨hsupport t s hv,hv⟩
    exact ⟨u,(congrArg (fun v => fun j => (v j).val) hu).trans hx,
      (congrArg (fun v => fun j => (v j).val) hs).trans hy⟩
  · rintro ⟨u,hu,hv⟩
    exact ⟨u.val,gammaVolumeValue P.toGamma.toGammaRVObject u,
      ((P.graph_iff u.val (P.volume u).val).mp ⟨u,rfl,rfl⟩).2,hu,hv⟩

theorem GammaFiniteRVSchema.exists_valid_bound {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (F : GammaFiniteRVSchema B p a k sp) (z : Fin p → M) (hz : ∀ j, sortEval (sp j) (z j))
    (hsupport : ∀ x y, F.rowVolume z x y → x ∈ F.rowDomain z)
    (P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ a k
      (F.rowDomain z) (F.rowVolume z)) :
    ∃ bound : ℕ, (F.withBound bound).valid z := by
  let C : Base (M := M) := ⟨B.real ∪ Set.range z,B.gamma⟩
  have hsmall : Cardinal.mk C.real < κ := small_union_range hκ B.real hreal z
  obtain ⟨bound,hN⟩ := @gammaRawObjectVolume_uniform_bound M sM hM C k κ hκ hs hsmall hgamma P.toGamma
  have hD := F.raw_row_domain_presented z P
  have hV := F.raw_row_volume_presented z hsupport P
  refine ⟨bound,hz,?_,?_,?_⟩
  · intro x hx
    obtain ⟨y,hy,hu⟩ := gammaRawObjectVolume_unique P.toGamma.toGammaRVObject x ((hD x).mp hx)
    exact ⟨y,(hV x y).mpr hy,fun y' hy' => hu y' ((hV x y').mp hy')⟩
  · intro x y hxy
    obtain ⟨u,hu,_⟩ := (gammaRawObjectVolume_append_iff P.toGamma.toGammaRVObject x y).mp ((hV x y).mp hxy)
    exact (hD x).mpr ⟨u,hu⟩
  · intro y hy
    have he : {x | Fin.append (Fin.append z x) y ∈ F.volume} =
        {x | Fin.append x y ∈ gammaRawObjectVolume P.toGamma.toGammaRVObject} := Set.ext (fun x => hV x y)
    change {x | Fin.append (Fin.append z x) y ∈ F.volume}.Finite ∧
      {x | Fin.append (Fin.append z x) y ∈ F.volume}.ncard ≤ bound
    rw [he]
    exact hN y hy

end IntegrationInACVF.Section6
