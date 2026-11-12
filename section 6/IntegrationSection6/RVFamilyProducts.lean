import IntegrationSection6.GammaFamilyCoordinates
import IntegrationSection6.MixedCoordinatePointMaps
import IntegrationSection6.GammaSchemaFiniteRowPresentations

/-! Products of actual finite RV-family formulas preserve the shared VF
parameter tuple and concatenate both payload and volume coordinates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b k l : ℕ}

def GammaRVFamilyFormula.product (F : GammaRVFamilyFormula B p a k) (G : GammaRVFamilyFormula B p b l) :
    GammaRVFamilyFormula B p (a+b) (k+l) where
  domain := {x | (x.1,x.2 ∘ Fin.castAdd b) ∈ F.domain ∧ (x.1,x.2 ∘ Fin.natAdd a) ∈ G.domain}
  domain_definable := (gammaLogicInput B).inter
    (gamma_global_preimage (mixedCoordinatePointMap (Equiv.refl _) (Fin.castAdd b) B.real) F.domain_definable)
    (gamma_global_preimage (mixedCoordinatePointMap (Equiv.refl _) (Fin.natAdd a) B.real) G.domain_definable)
  volume := fun x y => F.volume (x.1,x.2 ∘ Fin.castAdd b) (Fin.elim0,y.2 ∘ Fin.castAdd l) ∧
    G.volume (x.1,x.2 ∘ Fin.natAdd a) (Fin.elim0,y.2 ∘ Fin.natAdd k)
  volume_definable := by
    have h :=
      (F.volume_definable.preimage_maps
      (mixedCoordinatePointMap (Equiv.refl _) (Fin.castAdd b) B.real)
      (mixedCoordinatePointMap (Fin.elim0 : Fin 0 → Fin 0) (Fin.castAdd l) B.real)).inter
      (G.volume_definable.preimage_maps
      (mixedCoordinatePointMap (Equiv.refl _) (Fin.natAdd a) B.real)
      (mixedCoordinatePointMap (Fin.elim0 : Fin 0 → Fin 0) (Fin.natAdd k) B.real))
    apply GammaGraphDefinable.congr h
    intro x y
    have he : y.1 ∘ (Fin.elim0 : Fin 0 → Fin 0) = (Fin.elim0 : Fin 0 → VF (M := M)) := Subsingleton.elim _ _
    simpa only [mixedCoordinatePointMap_value,Function.comp_id,Equiv.coe_refl,he]

def GammaFiniteRVSchema.productFormula (F : GammaFiniteRVSchema B p a k) (G : GammaFiniteRVSchema B p b l) :=
  (F.toFamily.product G.toFamily).schema 0

theorem GammaFiniteRVSchema.product_row_domain (F : GammaFiniteRVSchema B p a k) (G : GammaFiniteRVSchema B p b l)
    (x : Fin p → VF (M := M)) (r : Fin (a+b) → RV (M := M)) :
    r ∈ (F.productFormula G).rowDomain (fun j => (x j).val) ↔
      (r ∘ Fin.castAdd b) ∈ F.rowDomain (fun j => (x j).val) ∧
      (r ∘ Fin.natAdd a) ∈ G.rowDomain (fun j => (x j).val) := by
  exact (F.toFamily.product G.toFamily).schema_domain 0 (x,r)

theorem GammaFiniteRVSchema.product_row_volume (F : GammaFiniteRVSchema B p a k) (G : GammaFiniteRVSchema B p b l)
    (x : Fin p → VF (M := M)) (r : Fin (a+b) → RV (M := M)) (v : Fin (k+l) → RV (M := M)) :
    (F.productFormula G).rowVolume (fun j => (x j).val) r v ↔
      F.rowVolume (fun j => (x j).val) (r ∘ Fin.castAdd b) (v ∘ Fin.castAdd l) ∧
      G.rowVolume (fun j => (x j).val) (r ∘ Fin.natAdd a) (v ∘ Fin.natAdd k) := by
  exact (F.toFamily.product G.toFamily).schema_volume 0 (x,r) (Fin.elim0,v)

theorem GammaFiniteRVSchema.finiteRow_product (F : GammaFiniteRVSchema B p a k) (G : GammaFiniteRVSchema B p b l)
    (x : Fin p → VF (M := M)) (hF : F.finiteRow (fun j => (x j).val)) (hG : G.finiteRow (fun j => (x j).val)) :
    (F.productFormula G).finiteRow (fun j => (x j).val) := by
  refine ⟨?_,?_,?_⟩
  · intro r hr
    obtain ⟨v,hv,hvu⟩ := hF.1 _ ((F.product_row_domain G x r).mp hr).1
    obtain ⟨w,hw,hwu⟩ := hG.1 _ ((F.product_row_domain G x r).mp hr).2
    refine ⟨Fin.append v w,(F.product_row_volume G x r _).mpr ?_,?_⟩
    · simpa only [Function.comp_def,Fin.append_left,Fin.append_right] using And.intro hv hw
    · intro t ht
      obtain ⟨htv,htw⟩ := (F.product_row_volume G x r t).mp ht
      have hl := hvu _ htv
      have hr := hwu _ htw
      exact Fin.append_castAdd_natAdd.symm.trans (congrArg₂ Fin.append hl hr)
  · intro r v hv
    obtain ⟨hf,hg⟩ := (F.product_row_volume G x r v).mp hv
    exact (F.product_row_domain G x r).mpr ⟨hF.2.1 _ _ hf,hG.2.1 _ _ hg⟩
  · intro v
    apply (((hF.2.2 (v ∘ Fin.castAdd l)).prod (hG.2.2 (v ∘ Fin.natAdd k))).image
      (fun t => Fin.append t.1 t.2)).subset
    intro r hr
    exact ⟨(r ∘ Fin.castAdd b,r ∘ Fin.natAdd a),(F.product_row_volume G x r v).mp hr,Fin.append_castAdd_natAdd⟩

end IntegrationInACVF.Section6
