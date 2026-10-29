import Mathlib

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Clawfree
namespace Base

abbrev Vertex := Fin 12

def row : Vertex → Fin 3 := ![0, 0, 0, 1, 1, 1, 2, 2, 2, 0, 1, 2]
def col : Vertex → Fin 3 := ![0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2]

def adjacent (u v : Vertex) : Prop :=
  u ≠ v ∧ (row u = row v ∨ col u = col v)

instance (u v : Vertex) : Decidable (adjacent u v) := by
  unfold adjacent
  infer_instance

def graph : SimpleGraph Vertex where
  Adj := adjacent
  symm := by
    intro u v h
    exact ⟨fun hvu => h.1 hvu.symm,
      h.2.elim (fun hr => Or.inl hr.symm) (fun hc => Or.inr hc.symm)⟩
  loopless := by
    intro u h
    exact h.1 rfl

def ClawFree : Prop :=
  ∀ v a b c : Vertex, a ≠ b → a ≠ c → b ≠ c →
    adjacent v a → adjacent v b → adjacent v c →
    adjacent a b ∨ adjacent a c ∨ adjacent b c

def Proper {q : ℕ} (c : Vertex → Fin q) : Prop :=
  ∀ u v : Vertex, adjacent u v → c u ≠ c v

def BColoring {q : ℕ} (c : Vertex → Fin q) : Prop :=
  Proper c ∧ ∀ a : Fin q, ∃ v : Vertex,
    c v = a ∧ ∀ b : Fin q, b ≠ a →
      ∃ w : Vertex, adjacent v w ∧ c w = b

instance {q : ℕ} (c : Vertex → Fin q) : Decidable (Proper c) := by
  unfold Proper
  infer_instance

instance {q : ℕ} (c : Vertex → Fin q) : Decidable (BColoring c) := by
  unfold BColoring
  infer_instance

def color4 : Vertex → Fin 4 := ![0, 1, 2, 2, 0, 1, 1, 2, 0, 3, 3, 3]
def color6 : Vertex → Fin 6 := ![0, 4, 2, 5, 2, 0, 3, 1, 4, 1, 3, 5]

theorem clawFree : ClawFree := by unfold ClawFree; native_decide
theorem b4 : BColoring color4 := by native_decide
theorem b6 : BColoring color6 := by native_decide

end Base
end Clawfree

namespace Clawfree
namespace Base

def complete (f : Fin 8 → Fin 5) : Vertex → Fin 5 :=
  ![0, 1, 2, f 0, f 1, f 2, f 3, f 4, f 5, 3, f 6, f 7]

theorem normalized_no_five :
    ∀ f : Fin 8 → Fin 5, ¬ BColoring (complete f) := by
  native_decide

end Base
end Clawfree

namespace Clawfree
namespace Base

theorem rename {q : ℕ} {c : Vertex → Fin q}
    (p : Fin q → Fin q) (hp : Function.Bijective p)
    (hc : BColoring c) : BColoring (fun v => p (c v)) := by
  constructor
  · intro u v huv heq
    exact hc.1 u v huv (hp.1 heq)
  · intro a
    rcases hp.2 a with ⟨a', rfl⟩
    rcases hc.2 a' with ⟨v, hv, hw⟩
    refine ⟨v, congrArg p hv, ?_⟩
    intro b hba
    rcases hp.2 b with ⟨b', rfl⟩
    have hne : b' ≠ a' := by
      intro h
      exact hba (congrArg p h)
    rcases hw b' hne with ⟨w, hadj, hcw⟩
    exact ⟨w, hadj, congrArg p hcw⟩

def paletteMap (a b c d z : Fin 5) : Fin 5 :=
  if z = a then 0 else if z = b then 1 else
  if z = c then 2 else if z = d then 3 else 4

def PaletteInjective (a b c d : Fin 5) : Prop :=
  ∀ x y : Fin 5, paletteMap a b c d x = paletteMap a b c d y → x = y

instance (a b c d : Fin 5) : Decidable (PaletteInjective a b c d) := by
  unfold PaletteInjective
  infer_instance

theorem paletteCheck : ∀ a b c d : Fin 5,
    (a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d) →
    PaletteInjective a b c d := by
  native_decide

theorem normalize_four :
    ∀ a b c d : Fin 5,
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      ∃ p : Fin 5 → Fin 5,
        Function.Bijective p ∧ p a = 0 ∧ p b = 1 ∧ p c = 2 ∧ p d = 3 := by
  intro a b c d hab hac had hbc hbd hcd
  have hi : Function.Injective (paletteMap a b c d) := by
    intro x y hxy
    exact paletteCheck a b c d ⟨hab, hac, had, hbc, hbd, hcd⟩ x y hxy
  refine ⟨paletteMap a b c d, ⟨hi, Finite.surjective_of_injective hi⟩,
    ?_, ?_, ?_, ?_⟩
  · simp [paletteMap]
  · simp [paletteMap, Ne.symm hab]
  · simp [paletteMap, Ne.symm hac, Ne.symm hbc]
  · simp [paletteMap, Ne.symm had, Ne.symm hbd, Ne.symm hcd]

theorem no_five (c : Vertex → Fin 5) : ¬ BColoring c := by
  intro hc
  have h01 : c 0 ≠ c 1 := hc.1 0 1 (by decide)
  have h02 : c 0 ≠ c 2 := hc.1 0 2 (by decide)
  have h09 : c 0 ≠ c 9 := hc.1 0 9 (by decide)
  have h12 : c 1 ≠ c 2 := hc.1 1 2 (by decide)
  have h19 : c 1 ≠ c 9 := hc.1 1 9 (by decide)
  have h29 : c 2 ≠ c 9 := hc.1 2 9 (by decide)
  obtain ⟨p, hp, h0, h1, h2, h9⟩ :=
    normalize_four (c 0) (c 1) (c 2) (c 9) h01 h02 h09 h12 h19 h29
  let d : Vertex → Fin 5 := fun v => p (c v)
  have hd : BColoring d := rename p hp hc
  have hd0 : d 0 = 0 := h0
  have hd1 : d 1 = 1 := h1
  have hd2 : d 2 = 2 := h2
  have hd9 : d 9 = 3 := h9
  let f : Fin 8 → Fin 5 := ![d 3, d 4, d 5, d 6, d 7, d 8, d 10, d 11]
  have heq : complete f = d := by
    funext v
    fin_cases v <;> simp [complete, f, hd0, hd1, hd2, hd9]
  apply normalized_no_five f
  rw [heq]
  exact hd

def HasBColoring (q : ℕ) : Prop := ∃ c : Vertex → Fin q, BColoring c

def BContinuous : Prop :=
  ∀ a b : ℕ, HasBColoring a → HasBColoring b →
    ∀ q : ℕ, a ≤ q → q ≤ b → HasBColoring q

theorem noBColoring5 : ¬ HasBColoring 5 := by
  rintro ⟨c, hc⟩
  exact no_five c hc

theorem not_bContinuous : ¬ BContinuous := by
  intro h
  exact noBColoring5
    (h 4 6 ⟨color4, b4⟩ ⟨color6, b6⟩ 5 (by decide) (by decide))

theorem counterexample :
    ClawFree ∧ HasBColoring 4 ∧ HasBColoring 6 ∧
    ¬ HasBColoring 5 ∧ ¬ BContinuous :=
  ⟨clawFree, ⟨color4, b4⟩, ⟨color6, b6⟩, noBColoring5, not_bContinuous⟩

end Base
end Clawfree
