import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_736

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

def rn (f : ℕ → ℕ) (g : Gate) : Gate := { op := g.op, inputs := g.inputs.map f }

theorem getD_append_lt (w b : List Bool) (i : ℕ) (h : i < w.length) :
    (w ++ b).getD i false = w.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_ge (w : List Bool) (i : ℕ) (h : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem getD_last (w : List Bool) (b : Bool) : (w ++ [b]).getD w.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem sim (f : ℕ → ℕ) : ∀ (gs : List Gate) (w w' : List Bool),
    (∀ i, w'.getD (f i) false = w.getD i false) →
    (∀ i, i < w.length → f i < w'.length) →
    (∀ t, t < gs.length → f (w.length + t) = w'.length + t) →
    (∀ i, w.length + gs.length ≤ i → w'.length + gs.length ≤ f i) →
    ∀ i, (wf (gs.map (rn f)) w').getD (f i) false = (wf gs w).getD i false
  | [], w, w', hA, _, _, _ => by
    intro i
    exact hA i
  | g :: gs, w, w', hA, hB, hf, hbig => by
    have key : (rn f g).op.eval ((rn f g).inputs.map fun i => w'.getD i false)
        = g.op.eval (g.inputs.map fun i => w.getD i false) := by
      simp only [rn, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact hA i
    have h0 : f w.length = w'.length := by
      have := hf 0 (by simp)
      simpa using this
    have hA1 : ∀ i, (w' ++ [(rn f g).op.eval ((rn f g).inputs.map fun i => w'.getD i false)]).getD
        (f i) false = (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).getD i false := by
      intro i
      rcases lt_trichotomy i w.length with hi | hi | hi
      · rw [getD_append_lt _ _ _ (hB i hi), getD_append_lt _ _ _ hi, hA i]
      · subst hi
        rw [h0, key, getD_last, getD_last]
      · have hge : w'.length + 1 ≤ f i := by
          by_cases hlt : i < w.length + (g :: gs).length
          · have := hf (i - w.length) (by omega)
            rw [show w.length + (i - w.length) = i by omega] at this
            omega
          · have := hbig i (by omega)
            simp only [List.length_cons] at this
            omega
        rw [getD_ge _ _ (by simp only [List.length_append, List.length_singleton]; omega),
          getD_ge _ _ (by simp only [List.length_append, List.length_singleton]; omega)]
    have hB1 : ∀ i, i < (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).length →
        f i < (w' ++ [(rn f g).op.eval ((rn f g).inputs.map fun i => w'.getD i false)]).length := by
      intro i hi
      simp only [List.length_append, List.length_singleton] at hi ⊢
      rcases Nat.lt_or_ge i w.length with h | h
      · have := hB i h
        omega
      · have : i = w.length := by omega
        subst this
        omega
    have hf1 : ∀ t, t < gs.length →
        f ((w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).length + t)
          = (w' ++ [(rn f g).op.eval ((rn f g).inputs.map fun i => w'.getD i false)]).length + t := by
      intro t ht
      have := hf (t + 1) (by simp only [List.length_cons]; omega)
      simp only [List.length_append, List.length_singleton]
      rw [show w.length + 1 + t = w.length + (t + 1) by omega, this]
      omega
    have hbig1 : ∀ i, (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).length + gs.length ≤ i →
        (w' ++ [(rn f g).op.eval ((rn f g).inputs.map fun i => w'.getD i false)]).length
          + gs.length ≤ f i := by
      intro i hi
      simp only [List.length_append, List.length_singleton] at hi ⊢
      have := hbig i (by simp only [List.length_cons]; omega)
      simp only [List.length_cons] at this
      omega
    intro i
    exact sim f gs _ _ hA1 hB1 hf1 hbig1 i

end PEqualNP.Outside.L_meta_736

theorem PEqualNP.Outside.L_meta_736 : ∀ (n n' : ℕ) (O : Finset (Fin n)) (e : Fin n' → Fin n), StrictMono e →
  (∀ k : Fin n, k ∉ O ↔ ∃ j : Fin n', e j = k) → n' + O.card = n →
  ∀ gates : List PEqualNP.CircuitLowerBounds.Gate,
  ∃ psi : ℕ → ℕ, ∀ x x' : List Bool, x.length = n → x'.length = n' →
    (∀ k ∈ O, x.getD (k : ℕ) false = true) →
    (∀ j : Fin n', x.getD (e j : ℕ) false = x'.getD (j : ℕ) false) →
    (∀ i : ℕ, (PEqualNP.CircuitLowerBounds.Circuit.wires
        { gates := { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] } ::
            gates.map (fun g => { op := g.op, inputs := g.inputs.map psi }), output := 0 } x').getD (psi i) false
      = (PEqualNP.CircuitLowerBounds.Circuit.wires { gates := gates, output := 0 } x).getD i false) ∧
    (∀ o : ℕ, PEqualNP.CircuitLowerBounds.Circuit.eval
        { gates := { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] } ::
            gates.map (fun g => { op := g.op, inputs := g.inputs.map psi }), output := psi o } x'
      = PEqualNP.CircuitLowerBounds.Circuit.eval { gates := gates, output := o } x) := by
  intro n n' O e _ hOe _ gates
  classical
  let psi : ℕ → ℕ := fun i =>
    if h : i < n then
      (if hO : (⟨i, h⟩ : Fin n) ∈ O then n' else ((hOe ⟨i, h⟩).1 hO).choose.val)
    else if i < n + gates.length then n' + 1 + (i - n) else n' + 1 + gates.length
  refine ⟨psi, ?_⟩
  intro x x' hx hx' hO hxx'
  have hlen : (x' ++ [true]).length = n' + 1 := by simp [hx']
  have hA : ∀ i, (x' ++ [true]).getD (psi i) false = x.getD i false := by
    intro i
    by_cases h : i < n
    · by_cases hO' : (⟨i, h⟩ : Fin n) ∈ O
      · have hp : psi i = n' := by
          simp only [psi]
          rw [dif_pos h, dif_pos hO']
        rw [hp, ← hx', PEqualNP.Outside.L_meta_736.getD_last]
        exact (hO ⟨i, h⟩ hO').symm
      · have hex := (hOe ⟨i, h⟩).1 hO'
        have hp : psi i = ((hOe ⟨i, h⟩).1 hO').choose.val := by
          simp only [psi]
          rw [dif_pos h, dif_neg hO']
        have hej := ((hOe ⟨i, h⟩).1 hO').choose_spec
        rw [hp, PEqualNP.Outside.L_meta_736.getD_append_lt _ _ _
          (by rw [hx']; exact ((hOe ⟨i, h⟩).1 hO').choose.isLt)]
        have := hxx' ((hOe ⟨i, h⟩).1 hO').choose
        rw [hej] at this
        exact this.symm
    · have hge : n' + 1 ≤ psi i := by
        simp only [psi]
        rw [dif_neg h]
        split_ifs <;> omega
      rw [PEqualNP.Outside.L_meta_736.getD_ge _ _ (by rw [hlen]; exact hge),
        PEqualNP.Outside.L_meta_736.getD_ge _ _ (by rw [hx]; omega)]
  have hB : ∀ i, i < x.length → psi i < (x' ++ [true]).length := by
    intro i hi
    rw [hx] at hi
    rw [hlen]
    simp only [psi]
    rw [dif_pos hi]
    split_ifs with hO'
    · omega
    · have := ((hOe ⟨i, hi⟩).1 hO').choose.isLt
      omega
  have hf : ∀ t, t < gates.length → psi (x.length + t) = (x' ++ [true]).length + t := by
    intro t ht
    rw [hx, hlen]
    simp only [psi]
    rw [dif_neg (by omega), if_pos (by omega)]
    omega
  have hbig : ∀ i, x.length + gates.length ≤ i → (x' ++ [true]).length + gates.length ≤ psi i := by
    intro i hi
    rw [hx] at hi
    rw [hlen]
    simp only [psi]
    rw [dif_neg (by omega), if_neg (by omega)]
  have main := PEqualNP.Outside.L_meta_736.sim psi gates x (x' ++ [true]) hA hB hf hbig
  exact ⟨fun i => main i, fun o => main o⟩
