module

public import Integration7.HKZeroVolumeIntegration
public import Integration7.OrdinaryFiniteProductIsomorphisms
public import Integration7.ZeroVFVolumeClassProducts
public import Integration7.VolumeFormProducts
public import Integration7.HKVolumeDataRelabeling
public import Integration7.MixedDomainProductJacobians

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Concrete Cartesian product of arbitrary weighted zero VF objects.
Both full mixed presentations and both RV forms are retained. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

def zeroVFProduct (A B : ZeroVFVolumeObject (M := M) S) : ZeroVFVolumeObject (M := M) S where
  underlying := vfFiniteProductObject (rawRVSpace (M := M) 1) A.underlying B.underlying
  form := (A.form.prod B.form).pullback (mixedUnpack A.underlying.obj.obj.set B.underlying.obj.obj.set)

theorem zeroVFProduct_density_pair (A B : ZeroVFVolumeObject (M := M) S)
    (u : A.underlying.obj.obj.set) (v : B.underlying.obj.obj.set) :
    (zeroVFProduct A B).form.value
      ((mixedPack A.underlying.obj.obj.set B.underlying.obj.obj.set).toImage
        ⟨(u.val,v.val),u.property,v.property⟩) = A.form.value u * B.form.value v := by
  change (A.form.prod B.form).value (mixedUnpack _ _
    ((mixedPack _ _).toImage ⟨(u.val,v.val),u.property,v.property⟩)) = _
  rw [mixedUnpack_pack]
  rfl

def zeroVFProductIso {A A' B B' : ZeroVFVolumeObject (M := M) S}
    (f : ZeroVFVolumeIso A A') (g : ZeroVFVolumeIso B B') :
    ZeroVFVolumeIso (zeroVFProduct A B) (zeroVFProduct A' B') where
  iso := ordinaryFiniteProductIso f.iso g.iso
  density w := by
    obtain ⟨uv,rfl⟩ := (mixedPackToImage_bijective A.underlying.obj.obj.set B.underlying.obj.obj.set).2 w
    let u := Map.prodFst A.underlying.obj.obj.set B.underlying.obj.obj.set uv
    let v := Map.prodSnd A.underlying.obj.obj.set B.underlying.obj.obj.set uv
    change (A.form.prod B.form).value (mixedUnpack _ _ ((mixedPack _ _).toImage uv)) =
      (A'.form.prod B'.form).value (mixedUnpack _ _ ((mixedPack _ _).toImage
        (Map.prodMap (finiteZeroVFMap f.iso) (finiteZeroVFMap g.iso)
          (mixedUnpack _ _ ((mixedPack _ _).toImage uv)))))
    rw [mixedUnpack_pack,mixedUnpack_pack]
    change A.form.value u * B.form.value v =
      A'.form.value (finiteZeroVFMap f.iso u) * B'.form.value (finiteZeroVFMap g.iso v)
    rw [f.density u,g.density v]

def zeroLiftProductIso (U V : ZeroRVVolumeObject (M := M) S) :
    ZeroVFVolumeIso (zeroVFProduct (zeroLift U) (zeroLift V)) (zeroLift (product S 0 0 U V)) where
  iso := ordinaryZeroLiftProductIso U.underlying V.underlying
  density w := by
    obtain ⟨uv,rfl⟩ := (mixedPackToImage_bijective (rvLift U.underlying.obj) (rvLift V.underlying.obj)).2 w
    let u := Map.prodFst (rvLift U.underlying.obj) (rvLift V.underlying.obj) uv
    let v := Map.prodSnd (rvLift U.underlying.obj) (rvLift V.underlying.obj) uv
    calc
      _ = (zeroLift U).form.value u * (zeroLift V).form.value v :=
        zeroVFProduct_density_pair (zeroLift U) (zeroLift V) u v
      _ = _ := ?_
    have hLabel : liftLabelMap (product S 0 0 U V).underlying.obj
        (finiteZeroVFMap (ordinaryZeroLiftProductIso U.underlying V.underlying)
          ((mixedPack _ _).toImage ⟨(u.val,v.val),u.property,v.property⟩)) =
        rvPackPair U.underlying.obj.domain V.underlying.obj.domain
          (liftLabelMap U.underlying.obj u) (liftLabelMap V.underlying.obj v) := Subtype.ext rfl
    change U.form.value (liftLabelMap U.underlying.obj u) * V.form.value (liftLabelMap V.underlying.obj v) =
      (product S 0 0 U V).form.value
        (liftLabelMap (product S 0 0 U V).underlying.obj
          (finiteZeroVFMap (ordinaryZeroLiftProductIso U.underlying V.underlying)
            ((mixedPack _ _).toImage ⟨(u.val,v.val),u.property,v.property⟩)))
    rw [hLabel]
    exact (product_density_pair 0 0 U V _ _).symm

end IntegrationInACVF.Section7.HK
