module

public import Integration7.GammaRVMapGraphOperations
public import Section4.RVProductMorphisms

@[expose] public section

/-! Cartesian products of actual raw RV maps retain their complete
original-Gamma graphs. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaGraphDefinable)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {S : Set M} {k l : ℕ}
variable {U U' : RVObject (M := M) S k} {V V' : RVObject (M := M) S l}

theorem RVMapGamma.prod {f : Map U.domain U'.domain} {g : Map V.domain V'.domain}
    (hf : RVMapGamma f P) (hg : RVMapGamma g P) : RVMapGamma (rvProductMap f g) P := by
  apply GammaGraphDefinable.congr (gamma_rv_relation_product hf hg)
  intro p q
  constructor
  · rintro ⟨⟨u,hu,hfu⟩,⟨v,hv,hgv⟩⟩
    let a : U.domain.prod V.domain := ⟨(u.val,v.val),u.property,v.property⟩
    let w := (rvPack U.domain V.domain).toImage a
    have hw : w.val = p.2 := (congrArg₂ Fin.append hu hv).trans Fin.append_castAdd_natAdd
    refine ⟨w,hw,?_⟩
    change ((rvPack U'.domain V'.domain).toImage (Map.prodMap f g (rvUnpack U.domain V.domain w))).val = q.2
    rw [rvUnpack_pack]
    exact (congrArg₂ Fin.append hfu hgv).trans Fin.append_castAdd_natAdd
  · rintro ⟨w,hw,hq⟩
    let a := rvUnpack U.domain V.domain w
    let u : U.domain := ⟨a.val.1,a.property.1⟩
    let v : V.domain := ⟨a.val.2,a.property.2⟩
    have hPack := congrArg Subtype.val (rvPack_unpack U.domain V.domain w)
    have hSource : Fin.append u.val v.val = p.2 := hPack.trans hw
    have hTarget : Fin.append (f u).val (g v).val = q.2 := hq
    refine ⟨⟨u,?_,?_⟩,⟨v,?_,?_⟩⟩
    · funext j
      exact (Fin.append_left u.val v.val j).symm.trans (congrFun hSource (Fin.castAdd V.arity j))
    · funext j
      exact (Fin.append_left (f u).val (g v).val j).symm.trans (congrFun hTarget (Fin.castAdd V'.arity j))
    · funext j
      exact (Fin.append_right u.val v.val j).symm.trans (congrFun hSource (Fin.natAdd U.arity j))
    · funext j
      exact (Fin.append_right (f u).val (g v).val j).symm.trans (congrFun hTarget (Fin.natAdd U'.arity j))

end IntegrationInACVF.Section7
