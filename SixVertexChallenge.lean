module

public import Mathlib

@[expose] public section

noncomputable section

namespace C145SixVertexPilot

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

def helmert : Fin 6 → Fin 6 → ℝ :=
  !![1,1,1,1,1,1; 1,-1,1,1,1,1; 1,0,-2,1,1,1;
     1,0,0,-3,1,1; 1,0,0,0,-4,1; 1,0,0,0,0,-5]
def gramWeight : Fin 6 → ℝ := ![6,2,6,12,20,30]
def port : Fin 6 → ℝ := ![99/101,20/101,0,0,0,0]
def literalRates : Fin 6 → ℝ := ![1,20,21,22,23,24]
def literalGenerator : Matrix (Fin 6) (Fin 6) ℝ :=
  fun v u => -(∑ i, literalRates i * helmert v i * helmert u i / gramWeight i)
def edgeWeight : Matrix (Fin 6) (Fin 6) ℝ := literalGenerator - Matrix.diagonal (fun v => literalGenerator v v)

/-- Identification of the explicit six-vertex source at decay one, with
its literal weights and signed port. Competitors may have any finite size
and must satisfy the stated connectedness, cyclicity and observation hypotheses. -/
theorem explicitSixVertexIdentification {n : ℕ} {T : ℝ}
    (hT : 0 < T)
    (W1 : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hs1 : W1.IsSymm) (hn1 : ∀ v u, 0 ≤ W1 v u)
    (hconnected1 : (supportGraph W1 hs1).Connected)
    (b1 : State n)
    (hcyclic1 : KrylovCyclic (generator 1 W1) b1)
    (R0 : Input T → Path 5 T) (R1 : Input T → Path n T)
    (hR0 : IsGraphResponse hT 1 edgeWeight port R0)
    (hR1 : IsGraphResponse hT 1 W1 b1 R1)
    (hc0 : ContinuousAt R0 0) (hc1 : ContinuousAt R1 0)
    (hData : TerminalJetsAgree hT port R0 b1 R1) :
    5 = n ∧ ∃ π : Fin 6 ≃ Fin (n+1),
      (∀ v u, generator 1 W1 (π v) (π u) = generator 1 edgeWeight v u) ∧
      (∀ v, b1 (π v) = port v) ∧
      (∀ v u, laplacian W1 (π v) (π u) = laplacian edgeWeight v u) ∧
      ((∀ v, W1 v v = 0) → ∀ v u, W1 (π v) (π u) = edgeWeight v u) := by
  sorry

end C145SixVertexPilot
end
end
