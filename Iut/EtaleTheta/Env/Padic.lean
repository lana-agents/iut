/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.Env.AutKernel

/-!
# Cyclotomic rigidity over `G_K` ([EtTh], Cor. 2.19(i), Cor. 2.18(iv))

The results of `Env/CycRigidity.lean` and `Env/AutKernel.lean` that use Prop. 2.14(i) assume the
augmentation target `G` to be center-free (hypothesis `hG`). For `G = G_K`, `K/ℚ_p` finite, this
is proved (`gK_center_free`, from the slimness of `G_K`, `PAdicGalois.isSlimGroup`), and the
hypothesis is removed here:

* `cyclotomicRigidity_env_padic`, `cyclotomicRigidity_envAut_padic` ([EtTh], Cor. 2.19(i));
* `ker_autPY_inlY_eq_padic` (automorphisms of the model environment over the identity of `Π_Y̲`
  act trivially on `μ_N`; [EtTh], proof of Cor. 2.18(iv)).
-/

namespace Iut.EtaleTheta.Env

open scoped commutatorElement

variable {p : ℕ} [Fact p.Prime] {E : IntermediateField ℚ_[p] (PadicAlgCl p)}
  [FiniteDimensional ℚ_[p] E]
  {PX μ : Type} [Group PX] [CommGroup μ] [TopologicalSpace PX] [IsTopologicalGroup PX]
  [TopologicalSpace μ] [DiscreteTopology μ]
  (aug : PX →* Iut.Frobenioid.PAdicGalois.GK p E)
  (ψ : Iut.Frobenioid.PAdicGalois.GK p E →* MulAut μ)
  (Kum : Subgroup (Iut.Frobenioid.PAdicGalois.GK p E → μ)) {PY PYdd : Subgroup PX}
  (hle : PYdd ≤ PY) (hψ : IsOpen ((act aug ψ).ker : Set PX)) (hKum : ∀ κ ∈ Kum, IsCocycle ψ κ)
  {η : PYdd → μ} (hη : IsCocycle (actDD aug ψ PYdd) η)

/-- **Cyclotomic rigidity** ([EtTh], Cor. 2.19(i)) over `G_K`: `cyclotomicRigidity_env` without
the center-freeness hypothesis. -/
theorem cyclotomicRigidity_env_padic [Finite μ] (hPY : Envelope.FISlim PY) [PY.Normal]
    (hsurj : ∀ σ, ∃ h ∈ PY, aug h = σ)
    (L Kθ : Subgroup PX) (hKL : Kθ ≤ L) (hLdd : L ≤ PYdd) (hLg : ∀ l ∈ L, aug l = 1)
    (hη13 : ∀ k (hk : k ∈ PYdd), k ∈ Kθ → η ⟨k, hk⟩ = 1)
    (hL : Subgroup.closure {c | c ∈ L ∧ ∃ a b, aug a = 1 ∧ b ∈ PY ∧ aug b = 1 ∧ c = ⁅a, b⁆} ⊔
      Kθ = L)
    {M : MonoThetaEnv.{0}} (f : MonoThetaEnv.Iso M (modelEnv aug ψ Kum hle hψ hKum hη))
    {Lsub Ksub Dsub : Subgroup M.G} (hLs : Lsub.map f.hom = rightSub aug ψ PY L)
    (hKs : Ksub.map f.hom = rightSub aug ψ PY Kθ) (hDs : Dsub.map f.hom = geomSub aug ψ PY)
    (t m : M.G) :
    M.IsCyc Lsub Ksub Dsub t m ↔ ∃ l : PYdd, (l : PX) ∈ L ∧
      f.e t = algSection aug ψ hle l ∧ f.e m = inlY aug ψ PY (η l)⁻¹ :=
  cyclotomicRigidity_env aug ψ Kum hle hψ hKum hη hPY gK_center_free hsurj L Kθ hKL hLdd hLg
    hη13 hL f hLs hKs hDs t m

/-- **No `(ℤ/N)^×`-indeterminacy** ([EtTh], Cor. 2.19(i)) over `G_K`. -/
theorem cyclotomicRigidity_envAut_padic [Finite μ] (hPY : Envelope.FISlim PY) [PY.Normal]
    (hsurj : ∀ σ, ∃ h ∈ PY, aug h = σ)
    (L Kθ : Subgroup PX) (hKL : Kθ ≤ L) (hLdd : L ≤ PYdd) (hLg : ∀ l ∈ L, aug l = 1)
    (hη13 : ∀ k (hk : k ∈ PYdd), k ∈ Kθ → η ⟨k, hk⟩ = 1)
    (hL : Subgroup.closure {c | c ∈ L ∧ ∃ a b, aug a = 1 ∧ b ∈ PY ∧ aug b = 1 ∧ c = ⁅a, b⁆} ⊔
      Kθ = L)
    (f : MonoThetaEnv.Iso (modelEnv aug ψ Kum hle hψ hKum hη)
      (modelEnv aug ψ Kum hle hψ hKum hη))
    (hLs : (rightSub aug ψ PY L).map f.hom = rightSub aug ψ PY L)
    (hKs : (rightSub aug ψ PY Kθ).map f.hom = rightSub aug ψ PY Kθ)
    (hDs : (geomSub aug ψ PY).map f.hom = geomSub aug ψ PY) (l : PYdd) (hl : (l : PX) ∈ L) :
    ∃ l' : PYdd, (l' : PX) ∈ L ∧ f.e (algSection aug ψ hle l) = algSection aug ψ hle l' ∧
      f.e (inlY aug ψ PY (η l)⁻¹) = inlY aug ψ PY (η l')⁻¹ :=
  cyclotomicRigidity_envAut aug ψ Kum hle hψ hKum hη hPY gK_center_free hsurj L Kθ hKL hLdd hLg
    hη13 hL f hLs hKs hDs l hl

/-- Automorphisms of the model environment over the identity of `Π_Y̲` act trivially on `μ_N`
([EtTh], proof of Cor. 2.18(iv), via Cor. 2.19(i)), over `G_K`. -/
theorem ker_autPY_inlY_eq_padic [Finite μ] (hPY : Envelope.FISlim PY) [PY.Normal]
    (hsurj : ∀ σ, ∃ h ∈ PY, aug h = σ)
    (L Kθ : Subgroup PX) (hKL : Kθ ≤ L) (hLdd : L ≤ PYdd) (hLg : ∀ l ∈ L, aug l = 1)
    (hη13 : ∀ k (hk : k ∈ PYdd), k ∈ Kθ → η ⟨k, hk⟩ = 1)
    (hL : Subgroup.closure {c | c ∈ L ∧ ∃ a b, aug a = 1 ∧ b ∈ PY ∧ aug b = 1 ∧ c = ⁅a, b⁆} ⊔
      Kθ = L)
    (hηL : ∀ m : μ, ∃ l : PYdd, (l : PX) ∈ L ∧ (η l)⁻¹ = m)
    {a : CategoryTheory.Aut (modelEnv aug ψ Kum hle hψ hKum hη)}
    (ha : a ∈ (autPY aug ψ Kum hle hψ hKum hη hPY).ker) (m : μ) :
    autE aug ψ Kum hle hψ hKum hη a (inlY aug ψ PY m) = inlY aug ψ PY m :=
  ker_autPY_inlY_eq gK_center_free hsurj L Kθ hKL hLdd hLg hη13 hL hηL ha m

end Iut.EtaleTheta.Env
