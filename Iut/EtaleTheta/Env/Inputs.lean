/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.Env.Padic

/-!
# Mono-theta environments with the inputs of the cyclotomic rigidity algorithm

The cyclotomic rigidity algorithm of [EtTh], Cor. 2.19(i) (`MonoThetaEnv.IsCyc`,
`Env/CycRigidity.lean`) takes, besides the environment `M`, the preimages in `Π` of the
subquotients of [EtTh], Cor. 2.18(i) (`l·Δ_Θ`, `Ker(Π_Y ↠ (Π_Y)^Θ)` and `Δ_Y`). In [EtTh] these
are reconstructed from `M` by a functorial group-theoretic algorithm; their reconstruction is a
Layer-B obligation (`Env/Transport.lean`: the reference subgroups are characteristic). This file
packages them for consumers that transport the algorithm along chains of isomorphisms
(`LogLink/Thm311Rest.lean`, IUT III, Thm. 3.11(iii)(c)):

* `MonoThetaEnv.Inputs M`: the three input subgroups of `M` (data);
* `Inputs.IsCyc`: the isomorphism of cyclotomes of `M` computed from these inputs;
* `Iso.Respects f I I'`: `f` maps the inputs `I` onto `I'` (for the genuine environments every
  isomorphism does, by [EtTh], Cor. 2.18(i)); `respects_refl`, `Respects.trans`,
  `Respects.symm`;
* `Iso.isCyc_inputs_iff`, `Iso.isCyc_inputs_symm`: **functoriality** of the algorithm;
* `Env.modelInputs`: the inputs of the model environment `modelEnv`;
  **`Env.isCyc_of_respects_padic`**: for every environment `M` with an isomorphism to the model
  over `G_K` respecting the inputs, the algorithmic isomorphism of cyclotomes of `M` is carried to
  the natural one `s^alg(l) ↦ η(l)⁻¹` ([EtTh], Cor. 2.19(i), from
  `cyclotomicRigidity_env_padic`).
-/

namespace Iut.EtaleTheta

universe u

namespace MonoThetaEnv

/-- **The inputs of the cyclotomic rigidity algorithm** for an environment `M`: the preimages in
`Π` of `l·Δ_Θ` (`L`), of `Ker(Π_Y ↠ (Π_Y)^Θ)` (`K`) and of `Δ_Y = Ker(Π_Y ↠ G_K)` (`D`)
([EtTh], Cor. 2.18(i)). -/
structure Inputs (M : MonoThetaEnv.{u}) where
  /-- The preimage of `l·Δ_Θ`. -/
  L : Subgroup M.G
  /-- The preimage of `Ker(Π_Y ↠ (Π_Y)^Θ)`. -/
  K : Subgroup M.G
  /-- The preimage of `Δ_Y`. -/
  D : Subgroup M.G

/-- **The isomorphism of cyclotomes** of `M` computed from the inputs `I` ([EtTh],
Cor. 2.19(i)). -/
def Inputs.IsCyc {M : MonoThetaEnv.{u}} (I : Inputs M) (t m : M.G) : Prop :=
  M.IsCyc I.L I.K I.D t m

/-- An isomorphism of environments **respects** the inputs `I`, `I'` if it maps each input
subgroup onto the corresponding one. -/
def Iso.Respects {M M' : MonoThetaEnv.{u}} (f : Iso M M') (I : Inputs M) (I' : Inputs M') :
    Prop :=
  I.L.map f.hom = I'.L ∧ I.K.map f.hom = I'.K ∧ I.D.map f.hom = I'.D

lemma Iso.map_refl {M : MonoThetaEnv.{u}} (H : Subgroup M.G) : H.map (Iso.refl M).hom = H := by
  ext x
  simp only [Subgroup.mem_map]
  exact ⟨fun ⟨y, hy, h⟩ => h ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩

lemma Iso.map_trans {M M' M'' : MonoThetaEnv.{u}} (f : Iso M M') (g : Iso M' M'')
    (H : Subgroup M.G) : H.map (f.trans g).hom = (H.map f.hom).map g.hom := by
  rw [Subgroup.map_map]
  rfl

lemma Iso.map_symm {M M' : MonoThetaEnv.{u}} (f : Iso M M') {H : Subgroup M.G}
    {H' : Subgroup M'.G} (h : H.map f.hom = H') : H'.map f.symm.hom = H := by
  rw [← h, Subgroup.map_map]
  ext x
  simp only [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    convert hy
    exact f.e.symm_apply_apply y
  · intro hx
    exact ⟨x, hx, f.e.symm_apply_apply x⟩

lemma Iso.respects_refl {M : MonoThetaEnv.{u}} (I : Inputs M) : (Iso.refl M).Respects I I :=
  ⟨Iso.map_refl _, Iso.map_refl _, Iso.map_refl _⟩

lemma Iso.Respects.trans {M M' M'' : MonoThetaEnv.{u}} {f : Iso M M'} {g : Iso M' M''}
    {I : Inputs M} {I' : Inputs M'} {I'' : Inputs M''} (hf : f.Respects I I')
    (hg : g.Respects I' I'') : (f.trans g).Respects I I'' := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [Iso.map_trans]
  · rw [hf.1, hg.1]
  · rw [hf.2.1, hg.2.1]
  · rw [hf.2.2, hg.2.2]

lemma Iso.Respects.symm {M M' : MonoThetaEnv.{u}} {f : Iso M M'} {I : Inputs M}
    {I' : Inputs M'} (hf : f.Respects I I') : f.symm.Respects I' I :=
  ⟨f.map_symm hf.1, f.map_symm hf.2.1, f.map_symm hf.2.2⟩

/-- **Functoriality of the isomorphism of cyclotomes** along isomorphisms respecting the
inputs ([EtTh], Cor. 2.19(i)). -/
theorem Iso.isCyc_inputs_iff {M M' : MonoThetaEnv.{u}} (f : Iso M M') {I : Inputs M}
    {I' : Inputs M'} (h : f.Respects I I') (t m : M.G) :
    I'.IsCyc (f.e t) (f.e m) ↔ I.IsCyc t m :=
  f.isCyc_iff h.1 h.2.1 h.2.2 t m

/-- Functoriality through the inverse of an isomorphism. -/
theorem Iso.isCyc_inputs_symm {M M' : MonoThetaEnv.{u}} (f : Iso M M') {I : Inputs M}
    {I' : Inputs M'} (h : f.Respects I I') (t m : M'.G) :
    I.IsCyc (f.e.symm t) (f.e.symm m) ↔ I'.IsCyc t m := by
  rw [← f.isCyc_inputs_iff h, f.e.apply_symm_apply, f.e.apply_symm_apply]

end MonoThetaEnv

namespace Env

variable {p : ℕ} [Fact p.Prime] {E : IntermediateField ℚ_[p] (PadicAlgCl p)}
  [FiniteDimensional ℚ_[p] E]
  {PX μ : Type} [Group PX] [CommGroup μ] [TopologicalSpace PX] [IsTopologicalGroup PX]
  [TopologicalSpace μ] [DiscreteTopology μ]
  (aug : PX →* Iut.Frobenioid.PAdicGalois.GK p E)
  (ψ : Iut.Frobenioid.PAdicGalois.GK p E →* MulAut μ)
  (Kum : Subgroup (Iut.Frobenioid.PAdicGalois.GK p E → μ)) {PY PYdd : Subgroup PX}
  (hle : PYdd ≤ PY) (hψ : IsOpen ((act aug ψ).ker : Set PX)) (hKum : ∀ κ ∈ Kum, IsCocycle ψ κ)
  {η : PYdd → μ} (hη : IsCocycle (actDD aug ψ PYdd) η)

/-- **The inputs of the model environment**: the preimages `rightSub L`, `rightSub Kθ` of
`L, Kθ ⊆ Π_X` and the geometric part `geomSub`. -/
noncomputable def modelInputs (L Kθ : Subgroup PX) :
    MonoThetaEnv.Inputs (modelEnv aug ψ Kum hle hψ hKum hη) where
  L := rightSub aug ψ PY L
  K := rightSub aug ψ PY Kθ
  D := geomSub aug ψ PY

open scoped commutatorElement in
/-- **Cyclotomic rigidity for environments with inputs** ([EtTh], Cor. 2.19(i)) over `G_K`: if
`f : M ≅ modelEnv` respects the inputs, the algorithmic isomorphism of cyclotomes of `M` is
carried to the natural one `s^alg(l) ↦ η(l)⁻¹` on `l·Δ_Θ`. The hypotheses are those of
`cyclotomicRigidity_env_padic` (Layer-B obligations of the theta setting). -/
theorem isCyc_of_respects_padic [Finite μ] (hPY : Envelope.FISlim PY) [PY.Normal]
    (hsurj : ∀ σ, ∃ h ∈ PY, aug h = σ)
    (L Kθ : Subgroup PX) (hKL : Kθ ≤ L) (hLdd : L ≤ PYdd) (hLg : ∀ l ∈ L, aug l = 1)
    (hη13 : ∀ k (hk : k ∈ PYdd), k ∈ Kθ → η ⟨k, hk⟩ = 1)
    (hL : Subgroup.closure {c | c ∈ L ∧ ∃ a b, aug a = 1 ∧ b ∈ PY ∧ aug b = 1 ∧ c = ⁅a, b⁆} ⊔
      Kθ = L)
    {M : MonoThetaEnv.{0}} (I : MonoThetaEnv.Inputs M)
    (f : MonoThetaEnv.Iso M (modelEnv aug ψ Kum hle hψ hKum hη))
    (hf : f.Respects I (modelInputs aug ψ Kum hle hψ hKum hη L Kθ)) (t m : M.G) :
    I.IsCyc t m ↔ ∃ l : PYdd, (l : PX) ∈ L ∧
      f.e t = algSection aug ψ hle l ∧ f.e m = inlY aug ψ PY (η l)⁻¹ :=
  cyclotomicRigidity_env_padic aug ψ Kum hle hψ hKum hη hPY hsurj L Kθ hKL hLdd hLg hη13 hL f
    hf.1 hf.2.1 hf.2.2 t m

end Env

end Iut.EtaleTheta
