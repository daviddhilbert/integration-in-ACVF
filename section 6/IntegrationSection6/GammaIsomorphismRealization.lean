import IntegrationSection6.GammaIsomorphismSchemata
import IntegrationSection6.GammaFiniteGraphIsomorphisms

/-! Valid chart rows give actual original-Gamma isomorphisms of RV[k]
objects, including both inherited finite volume-image conditions. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b k : ℕ} {sp : Fin p → SortTag}

def GammaFiniteRVIsoSchema.realizeChart (F : GammaFiniteRVIsoSchema B p a b k sp)
    (z : Fin p → M) (hz : F.valid z)
    (P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ a k
      (F.source.rowDomain z) (F.source.rowVolume z))
    (Q : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ b k
      (F.target.rowDomain z) (F.target.rowVolume z)) :
    GammaRVIso P.toGamma.toGammaRVObject Q.toGamma.toGammaRVObject := by
  let R (x : Fin a → RV (M := M)) (y : Fin b → RV (M := M)) : Prop :=
    Fin.append (Fin.append z (fun j => (x j).val)) (fun j => (y j).val) ∈ F.chart
  have hBij := hz.2.2.1
  have hPdom (u : P.domain) : u.val ∈ F.source.rowDomain z :=
    ((P.graph_iff u.val (P.volume u).val).mp ⟨u,rfl,rfl⟩).1
  have hQdom (v : Q.domain) : v.val ∈ F.target.rowDomain z :=
    ((Q.graph_iff v.val (Q.volume v).val).mp ⟨v,rfl,rfl⟩).1
  have hdom (x : Fin a → RV (M := M)) (y : Fin b → RV (M := M)) (hxy : R x y) :
      x ∈ (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M
        (@CanonicalStructure.normalize M sM) _ P.codes P.domain) ∧
      y ∈ (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M
        (@CanonicalStructure.normalize M sM) _ Q.codes Q.domain) := by
    have hx : Fin.append z (fun j => (x j).val) ∈ F.source.domain :=
      hBij.1.2.2.1 _ _ hxy
    have hy : Fin.append z (fun j => (y j).val) ∈ F.target.domain := (hBij.2 _).mpr ⟨_,hxy⟩
    exact ⟨(Set.ext_iff.mp P.domain_eq x).mpr hx,(Set.ext_iff.mp Q.domain_eq y).mpr hy⟩
  have hΓ := gamma_rv_tuple_relation_specialize sp z hz.1.1 F.chart_definable
  refine FiniteRV.gammaIsoOfFiniteRelation P.toGamma Q.toGamma R hΓ ?_ ?_ ?_ ?_ ?_
  · intro x y hxy
    exact ⟨⟨⟨x,(hdom x y hxy).1⟩,rfl⟩,⟨⟨y,(hdom x y hxy).2⟩,rfl⟩⟩
  · intro u
    obtain ⟨y,hy,hu⟩ := hBij.1.2.1 (fun j => (u.val j).val) (hPdom u)
    have hys (j : Fin b) : iRV (y j) := by
      simpa only [Fin.append_right,sortEval,iRV] using
        F.chart_definable.proper _ hy (Fin.natAdd (p+a) j)
    let yt : Fin b → RV (M := M) := fun j => ⟨y j,hys j⟩
    let v : Q.domain := ⟨yt,(hdom u.val yt hy).2⟩
    refine ⟨v,hy,?_⟩
    intro v' hv'
    apply Subtype.ext
    funext j
    apply Subtype.ext
    exact congrFun (hu (fun j => (v'.val j).val) hv') j
  · intro u u' v huv hu'v
    have hys (j : Fin b) : sortEval SortTag.rv (v.val j).val := by
      exact (@CanonicalStructure.sortEval_normalize M sM .rv _).mp (v.val j).property
    obtain ⟨x,hx,hu⟩ := bijectiveMapRowValid.unique_reverse hBij
      (fun j => (v.val j).val) (hQdom v) hys
    have he := (hu (fun j => (u.val j).val) huv).trans (hu (fun j => (u'.val j).val) hu'v).symm
    apply Subtype.ext
    funext j
    apply Subtype.ext
    exact congrFun he j
  · intro v
    obtain ⟨x,hx⟩ := (hBij.2 (fun j => (v.val j).val)).mp (hQdom v)
    have hxs (j : Fin a) : iRV (x j) := by
      simpa only [Fin.append_left,Fin.append_right,sortEval,iRV] using
        F.chart_definable.proper _ hx (Fin.castAdd b (Fin.natAdd p j))
    let xt : Fin a → RV (M := M) := fun j => ⟨x j,hxs j⟩
    exact ⟨⟨xt,(hdom xt v.val hx).1⟩,hx⟩
  · intro u v huv
    exact F.valid_weight hz u.val v.val
      (gammaVolumeValue P.toGamma.toGammaRVObject u) (gammaVolumeValue Q.toGamma.toGammaRVObject v) huv
      ((P.graph_iff u.val (P.volume u).val).mp ⟨u,rfl,rfl⟩).2
      ((Q.graph_iff v.val (Q.volume v).val).mp ⟨v,rfl,rfl⟩).2

theorem GammaFiniteRVIsoSchema.realize (F : GammaFiniteRVIsoSchema B p a b k sp)
    (z : Fin p → M) (hz : F.valid z) :
    Nonempty ((P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ a k
        (F.source.rowDomain z) (F.source.rowVolume z)) ×
      (Q : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ b k
        (F.target.rowDomain z) (F.target.rowVolume z)) ×
      GammaRVIso P.toGamma.toGammaRVObject Q.toGamma.toGammaRVObject) := by
  obtain ⟨P⟩ := F.source.realize z hz.1
  obtain ⟨Q⟩ := F.target.realize z hz.2.1
  exact ⟨⟨P,Q,F.realizeChart z hz P Q⟩⟩

end IntegrationInACVF.Section6
