import IntegrationSection4.GammaFamilySyntax
import IntegrationSection4.PreparedLinearity
import IntegrationSection3ACVF.RealParameterTuples

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section4.FamilyPreparedLinearity

open GammaRadiusAtomicity GammaLinearRestrictions GammaFamilySyntax

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {m l : ℕ}
variable {D : DefSet (M := M) S 1 m} {E : DefSet (M := M) S 1 l}

theorem source_labels (T : SpecialBijection D E) (a : D) (b : E)
    (he : SameRV (T.toMap a).val b.val) : labels a.val = labels (T.inverseMap b).val := by
  have hh := ((sameRV_iff _ _).mp (T.inverse_contractible (T.toMap a) b he)).2
  rw [T.inverse_apply] at hh
  exact congrArg (fun v : Fin m → RV (M := M) => fun i => (v i).val) hh

theorem body_subset (A : (Fin m → M) → Set M) (T : SpecialBijection D E)
    (hD : carrier D = domain A) (b : E) :
    InverseBodies.body T b ⊆ A (labels (T.inverseMap b).val) := by
  rintro x ⟨a,ha,he⟩
  have hh : (vfAt a.val 0).val ∈ A (labels a.val) :=
    (Set.ext_iff.mp hD a.val).mp a.property
  rw [source_labels T a b he,ha] at hh
  exact hh

theorem code_row_iff (A : (Fin m → M) → Set M) (f : (Fin m → M) → M → M)
    (hfVF : ∀ p x, x ∈ A p → iVF (f p x))
    (r s : M) (hr : NonzeroRV r) (hs : NonzeroRV s) (p : Point (M := M) 1 m) :
    linearRow A f p (Fin.elim0,![⟨r,hr.1⟩,⟨s,hs.1⟩]) ↔
      SlopeAt (A (labels p)) (f (labels p)) (hfVF (labels p))
        (vfAt p 0) (codeValue r) (codeValue s) := by
  change (NonzeroRV r ∧ NonzeroRV s ∧
    GammaLinearBallRow.row (A (labels p)) (f (labels p)) ![r,s,(vfAt p 0).val]) ↔ _
  exact ⟨fun h => (GammaLinearBallRow.row_iff _ _ _ r s hr hs _).mp h.2.2,
    fun h => ⟨hr,hs,(GammaLinearBallRow.row_iff _ _ _ r s hr hs _).mpr h⟩⟩

theorem rows_on_body (A : (Fin m → M) → Set M) (f : (Fin m → M) → M → M)
    (hfVF : ∀ p x, x ∈ A p → iVF (f p x)) (T : SpecialBijection D E)
    (hUniform : FiniteRelationPreparation.Uniform (linearRow A f) T)
    (b : E) (x y : VF (M := M)) (hx : x.val ∈ InverseBodies.body T b)
    (hy : y.val ∈ InverseBodies.body T b) (β s : Values.Gamma (M := M)) :
    SlopeAt (A (labels (T.inverseMap b).val)) (f (labels (T.inverseMap b).val))
      (hfVF _) x β s ↔
    SlopeAt (A (labels (T.inverseMap b).val)) (f (labels (T.inverseMap b).val))
      (hfVF _) y β s := by
  obtain ⟨r,hr,hrβ⟩ := EndpointLogic.codeValue_surjective β
  obtain ⟨u,hu,hus⟩ := EndpointLogic.codeValue_surjective s
  obtain ⟨a,ha,haKey⟩ := hx
  obtain ⟨c,hc,hcKey⟩ := hy
  let q : Point (M := M) 0 2 := (Fin.elim0,![⟨r,hr.1⟩,⟨u,hu.1⟩])
  have hh := hUniform (T.toMap a) (T.toMap c) (haKey.trans hcKey.symm) q
  rw [T.inverse_apply,T.inverse_apply] at hh
  have hax : vfAt a.val 0 = x := Subtype.ext ha
  have hcy : vfAt c.val 0 = y := Subtype.ext hc
  have hA := code_row_iff A f hfVF r u hr hu a.val
  have hC := code_row_iff A f hfVF r u hr hu c.val
  rw [hax,source_labels T a b haKey,hrβ,hus] at hA
  rw [hcy,source_labels T c b hcKey,hrβ,hus] at hC
  exact hA.symm.trans (hh.trans hC)

theorem linear_on_body {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : FullBaseAtomicity.Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (h00 : M ⊨ Axioms.ACVF00) (A : (Fin m → M) → Set M) (f : (Fin m → M) → M → M)
    (hf : FiniteScalarFamilies.Graph B A f) (hfVF : ∀ p x, x ∈ A p → iVF (f p x))
    (hInj : ∀ p, Set.InjOn (f p) (A p))
    (T : SpecialBijection D E) (hD : carrier D = domain A) (hE : IsRVPullback (carrier E))
    (hUniform : FiniteRelationPreparation.Uniform (linearRow A f) T) (b : E) :
    ∃ s : Values.Gamma (M := M), GammaLinearity.GammaLinear (InverseBodies.body T b)
      (f (labels (T.inverseMap b).val))
      (fun x hx => hfVF _ x (body_subset A T hD b hx)) s := by
  let p := labels (T.inverseMap b).val
  have hBA := body_subset A T hD b
  by_cases hb : vfAt b.val 0 = 0
  · refine ⟨1,?_⟩
    intro x y hx hy
    rw [InverseBodies.body_zero T b hb] at hx hy
    have he : y = x := Subtype.ext (hy.trans hx.symm)
    subst y
    simp only [sub_self,map_zero,mul_zero]
  · obtain ⟨γ,_,hBody⟩ := InverseBodies.body_ordinary T hE b hb
    let C := RealParameterTuples.extend B p
    have hh := FullBaseAtomicity.OverBase.preimage_comp hf
      (Sum.elim (Sum.elim Sum.inl (fun _ => .inr 0)) (fun _ => .inr 1) :
        (Fin m ⊕ Fin 1) ⊕ Fin 1 → Fin m ⊕ Fin 2)
    have hRow : FullBaseAtomicity.OverBase C (ImaginaryBaseImages.graphOn (A p) (f p)) :=
      RealParameterTuples.specialize B p hh
    have hBallA : gammaBall (vfAt (T.inverseMap b).val 0) γ true ⊆ A p := hBody ▸ hBA
    obtain ⟨s,hLin⟩ := ConstantRowsLinearity.on_ordinary_ball hκ hs C
      (RealParameterTuples.small hκ B hsmall p) h00 (A p) (f p) hRow (hfVF p) (hInj p)
      (vfAt (T.inverseMap b).val 0) γ hBallA (by
        intro x y hx hy β s
        exact rows_on_body A f hfVF T hUniform b x y (hBody.symm ▸ hx) (hBody.symm ▸ hy) β s)
    exact ⟨s,fun x y hx hy => hLin x y (hBody ▸ hx) (hBody ▸ hy)⟩

end IntegrationInACVF.Section4.FamilyPreparedLinearity
