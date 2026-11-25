module

public import Mathlib

@[expose] public section

noncomputable section

namespace C145Pilot

open Matrix MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup
  AddCommGroup.toAddCommMonoid
  NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace
  UniformSpace.toTopologicalSpace

abbrev State (n : ℕ) := Fin (n + 1) → ℝ
abbrev Time (T : ℝ) := Icc (0 : ℝ) T
abbrev Input (T : ℝ) := C(Time T, ℝ)
abbrev Path (n : ℕ) (T : ℝ) := C(Time T, State n)

def endTime (T : ℝ) (hT : 0 < T) : Time T :=
  ⟨T, hT.le, le_rfl⟩

def extendInput {T : ℝ} (hT : 0 < T) (f : Input T) (s : ℝ) : ℝ :=
  f (projIcc 0 T hT.le s)

def extendPath {n : ℕ} {T : ℝ} (hT : 0 < T)
    (u : Path n T) (s : ℝ) : State n :=
  u (projIcc 0 T hT.le s)

def restrictInput (T : ℝ) (g : ℝ → ℝ) (hg : Continuous g) : Input T :=
  ⟨fun t => g t, hg.comp continuous_subtype_val⟩

def observe {n : ℕ} (b x : State n) : ℝ := ∑ v, b v * x v

def rawFirst {n : ℕ} {T : ℝ} (b : State n)
    (R : Input T → Path n T) (g : Input T) (t : Time T) : ℝ :=
  deriv (fun ε : ℝ => observe b (R (ε • g) t)) 0

def rawMixed {n : ℕ} {T : ℝ} (b : State n)
    (R : Input T → Path n T) (g h : Input T) (t : Time T) : ℝ :=
  (1 / 2 : ℝ) * deriv
    (fun ε : ℝ => deriv (fun δ : ℝ => observe b (R (ε • g + δ • h) t)) 0) 0

def SmoothTemporalTest (T : ℝ) (g : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ tsupport g ⊆ Ioo (0 : ℝ) T

section WeightedGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

def laplacian (W : Matrix V V ℝ) : Matrix V V ℝ :=
  Matrix.diagonal (fun v => ∑ u, W v u) - W

def supportGraph (W : Matrix V V ℝ) (hs : W.IsSymm) : SimpleGraph V where
  Adj v u := v ≠ u ∧ 0 < W v u
  symm := ⟨by intro v u h; exact ⟨h.1.symm, by rw [hs.apply]; exact h.2⟩⟩
  loopless := ⟨by intro v h; exact h.1 rfl⟩

def KrylovCyclic (A : Matrix V V ℝ) (b : V → ℝ) : Prop :=
  Submodule.span ℝ (Set.range (fun k : ℕ => A^k *ᵥ b)) = ⊤

end WeightedGraph

def generator {n : ℕ} (μ : ℝ) (W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    Matrix (Fin (n+1)) (Fin (n+1)) ℝ := -μ • 1 - laplacian W

def graphVectorField {n : ℕ} (μ : ℝ)
    (W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (b : State n)
    (f : ℝ → ℝ) (t : ℝ) (x : State n) : State n :=
  fun v => (∑ w, generator μ W v w * x w) + x v ^ 2 + b v * f t

def IsGraphResponse {n : ℕ} {T : ℝ} (hT : 0 < T) (μ : ℝ)
    (W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (b : State n)
    (R : Input T → Path n T) : Prop :=
  R 0 = 0 ∧ ∀ᶠ f in 𝓝 (0 : Input T),
    extendPath hT (R f) 0 = 0 ∧ ∀ t ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath hT (R f))
        (graphVectorField μ W b (extendInput hT f) t (extendPath hT (R f) t))
        (Set.Icc (0 : ℝ) T) t

def NonGroundDecayBand {m : ℕ} (μ : ℝ)
    (W : Matrix (Fin (m+1)) (Fin (m+1)) ℝ) (ell u : ℝ) : Prop :=
  ∀ (r : ℝ) (x : Fin (m+1) → ℝ), x≠0 →
    generator μ W *ᵥ x=(-r) • x → r≠μ → ell≤r ∧ r≤u

section SourceCriterion

variable {n : ℕ}

def centeredPort (b : Fin (n+1) → ℝ) (v : Fin (n+1)) : ℝ :=
  b v - (∑ w, b w)/(n+1 : ℝ)

def sourceQChebyshevSq (b : Fin (n+1) → ℝ) (ell u delta : ℝ) : ℝ :=
  (((n+1 : ℕ)+2 : ℝ)*(∑ v, centeredPort b v^2)/(1024*delta^2))*
    ((u-ell)/(2*ell-u))^6

end SourceCriterion

def TerminalJetsAgree {m n : ℕ} {T : ℝ} (hT : 0 < T)
    (b0 : State m) (R0 : Input T → Path m T)
    (b1 : State n) (R1 : Input T → Path n T) : Prop :=
  (∀ (g : ℝ → ℝ) (hg : SmoothTemporalTest T g),
    rawFirst b0 R0 (restrictInput T g hg.1.continuous) (endTime T hT) =
      rawFirst b1 R1 (restrictInput T g hg.1.continuous) (endTime T hT)) ∧
  (∀ (g h : ℝ → ℝ) (hg : SmoothTemporalTest T g) (hh : SmoothTemporalTest T h),
    rawMixed b0 R0 (restrictInput T g hg.1.continuous) (restrictInput T h hh.1.continuous)
        (endTime T hT) =
      rawMixed b1 R1 (restrictInput T g hg.1.continuous) (restrictInput T h hh.1.continuous)
        (endTime T hT))

/-- C145 Theorem A with local response existence and identification for any
actual C² responses with equal terminal jets. The competitor is cyclic and may
have any finite size. The spectral band and contraction apply to the source. -/
theorem theoremA {m n : ℕ} {T : ℝ}
    (hT : 0 < T) (μ : ℝ) (hμ : 0 < μ)
    (W0 : Matrix (Fin (m+1)) (Fin (m+1)) ℝ)
    (W1 : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hs0 : W0.IsSymm) (hs1 : W1.IsSymm)
    (hn0 : ∀ v u, 0 ≤ W0 v u) (hn1 : ∀ v u, 0 ≤ W1 v u)
    (hc0 : (supportGraph W0 hs0).Connected) (hc1 : (supportGraph W1 hs1).Connected)
    (b0 : State m) (b1 : State n)
    (hcyc0 : KrylovCyclic (generator μ W0) b0)
    (hcyc1 : KrylovCyclic (generator μ W1) b1)
    (ell u : ℝ) (hw : ell < u) (hband : u < 2 * ell)
    (hSpectrum : NonGroundDecayBand μ W0 ell u)
    (delta : ℝ) (hd : 0 < delta)
    (hsep : ∀ j k, j ≠ k → delta ^ 2 ≤ (b0 j - b0 k) ^ 2)
    (hq : sourceQChebyshevSq b0 ell u delta < 1) :
    (∃ R0 : Input T → Path m T, IsGraphResponse hT μ W0 b0 R0 ∧ ContDiffAt ℝ 2 R0 0) ∧
    (∃ R1 : Input T → Path n T, IsGraphResponse hT μ W1 b1 R1 ∧ ContDiffAt ℝ 2 R1 0) ∧
    (∀ (R0 : Input T → Path m T) (R1 : Input T → Path n T),
      IsGraphResponse hT μ W0 b0 R0 → IsGraphResponse hT μ W1 b1 R1 →
      ContDiffAt ℝ 2 R0 0 → ContDiffAt ℝ 2 R1 0 → TerminalJetsAgree hT b0 R0 b1 R1 →
      m = n ∧ ∃ π : Fin (m+1) ≃ Fin (n+1),
        (∀ v u, generator μ W1 (π v) (π u) = generator μ W0 v u) ∧
        (∀ v, b1 (π v) = b0 v) ∧
        (∀ v u, laplacian W1 (π v) (π u) = laplacian W0 v u)) := by
  sorry

end C145Pilot
end
end
