import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_782

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_step_len (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma getD_append_left_lt (w t : List Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ t).getD i false = w.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_self (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (le_refl w.length)]
  simp

lemma getD_ge_len (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]

lemma foldl_step_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons]
    have hlt : i < (step w g).length := by
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [ih (step w g) hlt]
    exact getD_append_left_lt w _ i hi

lemma foldl_step_getD_ge (gs : List Gate) (w : List Bool) (i : ℕ) (hi : w.length + gs.length ≤ i) :
    (gs.foldl step w).getD i false = false := by
  apply getD_ge_len
  rw [foldl_step_len]
  exact hi

lemma foldl_step_gate (gs : List Gate) (w : List Bool) (j : ℕ) (g : Gate) (hj : gs[j]? = some g) :
    (gs.foldl step w).getD (w.length + j) false =
      g.op.eval (g.inputs.map fun i => if i < w.length + j then (gs.foldl step w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g0 gs ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      rw [Nat.add_zero, List.foldl_cons]
      have hlt : w.length < (step w g0).length := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [foldl_step_getD_lt gs (step w g0) w.length hlt]
      have hself : (step w g0).getD w.length false = g0.op.eval (g0.inputs.map fun i => w.getD i false) :=
        getD_append_self w _
      rw [hself]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · have hilt : i < (step w g0).length := by
          simp only [step, List.length_append, List.length_cons, List.length_nil]
          omega
        simp only [hi, ↓reduceIte, foldl_step_getD_lt gs (step w g0) i hilt]
        exact (getD_append_left_lt w _ i hi).symm
      · simp only [hi, ↓reduceIte]
        exact getD_ge_len w i (Nat.le_of_not_lt hi)
    | succ j' =>
      simp only [List.getElem?_cons_succ] at hj
      have hlen : (step w g0).length + j' = w.length + (j' + 1) := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [List.foldl_cons, ← hlen]
      exact ih (step w g0) j' hj

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl step x := rfl

lemma wires_gate_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) (g : Gate)
    (hj : C.gates[j]? = some g) :
    (C.wires (List.ofFn x)).getD (n + j) false =
      g.op.eval (g.inputs.map fun i => if i < n + j then (C.wires (List.ofFn x)).getD i false else false) := by
  have h := foldl_step_gate C.gates (List.ofFn x) j g hj
  simpa only [List.length_ofFn, ← wires_eq_foldl] using h

lemma ofFn_getD_lt {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (List.ofFn x).getD w false = x ⟨w, hw⟩ := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, ↓reduceDIte, Option.getD_some]

lemma wires_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (C.wires (List.ofFn x)).getD w false = x ⟨w, hw⟩ := by
  rw [wires_eq_foldl, foldl_step_getD_lt C.gates (List.ofFn x) w (by simp [hw]), ofFn_getD_lt]

lemma wires_oob {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : n + C.gates.length ≤ w) :
    (C.wires (List.ofFn x)).getD w false = false := by
  rw [wires_eq_foldl]
  exact foldl_step_getD_ge C.gates (List.ofFn x) w (by simp [hw])

lemma gateOp_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l : List ℕ) (f1 f2 : ℕ → Bool) (hle : ∀ i ∈ l, f1 i = true → f2 i = true) :
    op.eval (l.map f1) = true → op.eval (l.map f2) = true := by
  rcases hop with rfl | rfl
  · intro h
    change (l.map f1).all id = true at h
    change (l.map f2).all id = true
    rw [List.all_eq_true] at h ⊢
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact hle i hi (h _ (List.mem_map_of_mem hi))
  · intro h
    change (l.map f1).any id = true at h
    change (l.map f2).any id = true
    rw [List.any_eq_true] at h ⊢
    obtain ⟨b, hb, hbt⟩ := h
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact ⟨f2 i, List.mem_map_of_mem hi, hle i hi hbt⟩

lemma wires_mono {n : ℕ} (C : Circuit) (hmono : PEqualNP.MetaComplexity.Monotone2 C)
    (x y : Fin n → Bool) (hxy : ∀ u, x u = true → y u = true) :
    ∀ w : ℕ, (C.wires (List.ofFn x)).getD w false = true → (C.wires (List.ofFn y)).getD w false = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw1 : w < n
    · rw [wires_input C x w hw1, wires_input C y w hw1]
      exact hxy ⟨w, hw1⟩
    · by_cases hw2 : n + C.gates.length ≤ w
      · rw [wires_oob C x w hw2]
        intro h; exact absurd h (by decide)
      · have hjlt : w - n < C.gates.length := by omega
        set j := w - n
        have hwj : w = n + j := by omega
        have hg : C.gates[j]? = some (C.gates[j]'hjlt) := List.getElem?_eq_getElem hjlt
        have hgop : (C.gates[j]'hjlt).op = GateOp.and ∨ (C.gates[j]'hjlt).op = GateOp.or := by
          simpa using (hmono _ (List.mem_of_getElem? hg)).1
        rw [hwj, wires_gate_ofFn C x j _ hg, wires_gate_ofFn C y j _ hg]
        apply gateOp_mono _ hgop
        intro i _ hi
        by_cases hilt : i < n + j
        · simp only [hilt, ↓reduceIte] at hi ⊢
          exact ih i (by omega) hi
        · simp only [hilt, ↓reduceIte] at hi
          exact absurd hi (by decide)


def Good (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

def val {n : ℕ} (C : Circuit) (x : Fin n → Bool) (r : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD r false

def A (n : ℕ) (C : Circuit) (r : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun a : Fin n =>
    (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD r false = true)

lemma mem_A {n : ℕ} (C : Circuit) {a : Fin n} {r : ℕ} :
    a ∈ A n C r ↔ val C (fun b : Fin n => decide (b = a)) r = true := by
  simp [A, val]

def inp (n : ℕ) (C : Circuit) (r k : ℕ) : ℕ :=
  match C.gates[r - n]? with
  | some g => g.inputs.getD k 0
  | none => 0

def ch (n : ℕ) (C : Circuit) (r k : ℕ) : ℕ :=
  if inp n C r k < r then inp n C r k else n + C.gates.length

lemma ch_cases (n : ℕ) (C : Circuit) (r k : ℕ) :
    ch n C r k < r ∨ ch n C r k = n + C.gates.length := by
  unfold ch
  split_ifs with h
  · exact Or.inl h
  · exact Or.inr rfl

lemma ch_le (n : ℕ) (C : Circuit) (r k : ℕ) (hr : r ≤ n + C.gates.length) :
    ch n C r k ≤ n + C.gates.length := by
  rcases ch_cases n C r k with h | h <;> omega

lemma nmem_A_ge {n : ℕ} (C : Circuit) (r : ℕ) (a : Fin n) (h : n + C.gates.length ≤ r) :
    a ∉ A n C r := by
  intro ha
  rw [mem_A] at ha
  unfold val at ha
  rw [wires_oob C _ r h] at ha
  exact Bool.false_ne_true ha

lemma A_card_ge {n : ℕ} (C : Circuit) (r : ℕ) (h : n + C.gates.length ≤ r) :
    (A n C r).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha
  exact absurd ha (nmem_A_ge C r a h)

lemma A_card_input {n : ℕ} (C : Circuit) (r : ℕ) (hr : r < n) :
    (A n C r).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  rw [mem_A] at ha hb
  unfold val at ha hb
  rw [wires_input C _ r hr] at ha hb
  simp only [decide_eq_true_eq] at ha hb
  exact ha.symm.trans hb

lemma gate_eq {n : ℕ} (C : Circuit) (hC : Good C) (r : ℕ) (h1 : n ≤ r)
    (h2 : r < n + C.gates.length) :
    (∀ x : Fin n → Bool, val C x r = (val C x (ch n C r 0) && val C x (ch n C r 1))) ∨
    (∀ x : Fin n → Bool, val C x r = (val C x (ch n C r 0) || val C x (ch n C r 1))) := by
  have hj : r - n < C.gates.length := by omega
  obtain ⟨g, hg⟩ : ∃ g, C.gates[r - n]? = some g := ⟨_, List.getElem?_eq_getElem hj⟩
  obtain ⟨hop, hlen⟩ := hC g (List.mem_of_getElem? hg)
  obtain ⟨p, q, hpq⟩ := List.length_eq_two.mp hlen
  have hinp0 : inp n C r 0 = p := by simp [inp, hg, hpq]
  have hinp1 : inp n C r 1 = q := by simp [inp, hg, hpq]
  have key : ∀ x : Fin n → Bool,
      val C x r = g.op.eval [val C x (ch n C r 0), val C x (ch n C r 1)] := by
    intro x
    have hw := wires_gate_ofFn C x (r - n) g hg
    rw [show n + (r - n) = r by omega, hpq] at hw
    simp only [List.map_cons, List.map_nil] at hw
    have e1 : ∀ s : ℕ, (if s < r then (C.wires (List.ofFn x)).getD s false else false)
        = (C.wires (List.ofFn x)).getD (if s < r then s else n + C.gates.length) false := by
      intro s
      split_ifs
      · rfl
      · exact (wires_oob C x _ le_rfl).symm
    simp only [val, ch, hinp0, hinp1]
    rw [hw, e1 p, e1 q]
  rcases hop with h | h
  · left
    intro x
    rw [key x, h]
    simp [GateOp.eval]
  · right
    intro x
    rw [key x, h]
    simp [GateOp.eval]

def priv {n : ℕ} (C : Circuit) (Si : Finset (Fin n)) (r : ℕ) : Prop :=
  n ≤ r ∧ r < n + C.gates.length ∧ A n C r ⊆ Si ∧ 2 ≤ (A n C r).card

def stp {n : ℕ} (C : Circuit) (Si : Finset (Fin n)) (a b : ℕ) : Prop :=
  priv C Si a ∧ (b = ch n C a 0 ∨ b = ch n C a 1)

theorem per_output {n : ℕ} (C : Circuit) (hC : Good C) (Si : Finset (Fin n)) (o k c : ℕ)
    (h2 : 2 ≤ (A n C o).card) (hsub : A n C o ⊆ Si)
    (hprom : ∀ x : Fin n → Bool, (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k →
      (∀ q ∈ Si, x q = false) → val C x o = false)
    (hck : c ≤ k) (hcA : c + 1 ≤ (A n C o).card) :
    ∃ P : Finset ℕ, (∀ r ∈ P, priv C Si r) ∧ c ≤ P.card := by
  classical
  have hmono : PEqualNP.MetaComplexity.Monotone2 C := by
    unfold PEqualNP.MetaComplexity.Monotone2
    intro g hg
    obtain ⟨h1, h2⟩ := hC g hg
    refine ⟨?_, by omega⟩
    rcases h1 with h | h <;> simp [h]
  have ho : priv C Si o := by
    refine ⟨?_, ?_, hsub, h2⟩
    · by_contra h
      push_neg at h
      have := A_card_input C o h
      omega
    · by_contra h
      push_neg at h
      have := A_card_ge C o h
      omega
  have hreach_le : ∀ b, Relation.ReflTransGen (stp C Si) o b → b ≤ n + C.gates.length := by
    intro b hb
    induction hb with
    | refl => exact le_of_lt ho.2.1
    | tail _ hs _ =>
      obtain ⟨hpa, hb'⟩ := hs
      rcases hb' with h | h <;> rw [h] <;> exact ch_le n C _ _ (le_of_lt hpa.2.1)
  obtain ⟨P, hPdef⟩ : ∃ P : Finset ℕ, P = (Finset.range (n + C.gates.length)).filter
      (fun r => Relation.ReflTransGen (stp C Si) o r ∧ priv C Si r) := ⟨_, rfl⟩
  obtain ⟨X, hXdef⟩ : ∃ X : Finset ℕ, X = (Finset.range (n + C.gates.length + 1)).filter
      (fun r => Relation.ReflTransGen (stp C Si) o r ∧ ¬ priv C Si r) := ⟨_, rfl⟩
  have memP : ∀ r, r ∈ P ↔ r < n + C.gates.length ∧ Relation.ReflTransGen (stp C Si) o r ∧
      priv C Si r := by
    intro r
    rw [hPdef, Finset.mem_filter, Finset.mem_range]
  have memX : ∀ r, r ∈ X ↔ r < n + C.gates.length + 1 ∧ Relation.ReflTransGen (stp C Si) o r ∧
      ¬ priv C Si r := by
    intro r
    rw [hXdef, Finset.mem_filter, Finset.mem_range]
  have hoP : o ∈ P := (memP o).mpr ⟨ho.2.1, Relation.ReflTransGen.refl, ho⟩
  have hcount : X.card ≤ P.card + 1 := by
    have hsub2 : (P.erase o) ∪ X ⊆ (P ×ˢ (Finset.univ : Finset (Fin 2))).image
        (fun pk : ℕ × Fin 2 => ch n C pk.1 pk.2) := by
      intro r hr
      have hR : Relation.ReflTransGen (stp C Si) o r ∧ r ≠ o := by
        rcases Finset.mem_union.mp hr with h | h
        · obtain ⟨hne, hrP⟩ := Finset.mem_erase.mp h
          exact ⟨((memP r).mp hrP).2.1, hne⟩
        · obtain ⟨_, hRr, hnp⟩ := (memX r).mp h
          refine ⟨hRr, ?_⟩
          intro hro
          rw [hro] at hnp
          exact hnp ho
      obtain ⟨hRr, hne⟩ := hR
      rcases Relation.ReflTransGen.cases_tail hRr with h | ⟨b, hb, hs⟩
      · exact absurd h hne
      · obtain ⟨hbp, hb'⟩ := hs
        have hbP : b ∈ P := (memP b).mpr ⟨hbp.2.1, hb, hbp⟩
        rw [Finset.mem_image]
        rcases hb' with h | h
        · exact ⟨(b, 0), Finset.mem_product.mpr ⟨hbP, Finset.mem_univ _⟩, h.symm⟩
        · exact ⟨(b, 1), Finset.mem_product.mpr ⟨hbP, Finset.mem_univ _⟩, h.symm⟩
    have hdisj : Disjoint (P.erase o) X := by
      rw [Finset.disjoint_left]
      intro r hr hrX
      exact ((memX r).mp hrX).2.2 ((memP r).mp (Finset.mem_of_mem_erase hr)).2.2
    have hc1 := Finset.card_le_card hsub2
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_erase_of_mem hoP] at hc1
    have hc2 := Finset.card_image_le (s := P ×ˢ (Finset.univ : Finset (Fin 2)))
      (f := fun pk : ℕ × Fin 2 => ch n C pk.1 pk.2)
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fin] at hc2
    have hP1 : 1 ≤ P.card := Finset.card_pos.mpr ⟨o, hoP⟩
    omega
  refine ⟨P, fun r hr => ((memP r).mp hr).2.2, ?_⟩
  by_contra hlt
  push_neg at hlt
  have hXk : X.card ≤ k := by omega
  obtain ⟨XL, hXLdef⟩ : ∃ XL : Finset ℕ, XL = X.filter (fun r => ¬ A n C r ⊆ Si) := ⟨_, rfl⟩
  have memXL : ∀ r, r ∈ XL ↔ r ∈ X ∧ ¬ A n C r ⊆ Si := by
    intro r
    rw [hXLdef, Finset.mem_filter]
  have hpick : ∀ r ∈ XL, ∃ a, a ∈ A n C r ∧ a ∉ Si := by
    intro r hr
    exact Finset.not_subset.mp ((memXL r).mp hr).2
  have hne : Nonempty (Fin n) := by
    obtain ⟨a, _⟩ := Finset.card_pos.mp (by omega : 0 < (A n C o).card)
    exact ⟨a⟩
  choose! f hf using hpick
  obtain ⟨Y, hYdef⟩ : ∃ Y : Finset (Fin n), Y = XL.image f := ⟨_, rfl⟩
  obtain ⟨y, hydef⟩ : ∃ y : Fin n → Bool, ∀ q, y q = decide (q ∈ Y) := ⟨_, fun q => rfl⟩
  have hYk : Y.card ≤ k := by
    rw [hYdef]
    have hXL : XL.card ≤ X.card := by
      rw [hXLdef]
      exact Finset.card_filter_le _ _
    exact (Finset.card_image_le).trans (hXL.trans hXk)
  have hy1 : (Finset.univ.filter (fun q : Fin n => y q = true)).card ≤ k := by
    have : Finset.univ.filter (fun q : Fin n => y q = true) = Y := by
      ext q
      simp [hydef]
    rw [this]
    exact hYk
  have hy2 : ∀ q ∈ Si, y q = false := by
    intro q hq
    rw [hydef, decide_eq_false_iff_not]
    intro hqY
    rw [hYdef] at hqY
    obtain ⟨r, hr, hfr⟩ := Finset.mem_image.mp hqY
    rw [← hfr] at hq
    exact (hf r hr).2 hq
  have hy3 : ∀ r ∈ XL, val C y r = true := by
    intro r hr
    have h1 := (mem_A C).mp (hf r hr).1
    apply wires_mono C hmono (fun b : Fin n => decide (b = f r)) y _ r h1
    intro u hu
    have hu' : u = f r := by simpa using hu
    rw [hu', hydef, decide_eq_true_eq, hYdef]
    exact Finset.mem_image_of_mem f hr
  have hyo : val C y o = false := hprom y hy1 hy2
  have walk : ∀ g, Relation.ReflTransGen (stp C Si) o g → val C y g = false →
      ∀ a ∈ A n C g, ∃ r ∈ X, (A n C r).card ≤ 1 ∧ a ∈ A n C r := by
    intro g
    induction g using Nat.strong_induction_on with
    | _ g ih =>
    intro hg hyg a ha
    by_cases hpg : priv C Si g
    · have child : ∀ kk : ℕ, (ch n C g kk = ch n C g 0 ∨ ch n C g kk = ch n C g 1) →
          val C y (ch n C g kk) = false → a ∈ A n C (ch n C g kk) →
          ∃ r ∈ X, (A n C r).card ≤ 1 ∧ a ∈ A n C r := by
        intro kk hkk hy hac
        have hlt : ch n C g kk < g := by
          rcases ch_cases n C g kk with h | h
          · exact h
          · exact absurd hac (by rw [h]; exact nmem_A_ge C _ a le_rfl)
        exact ih _ hlt (Relation.ReflTransGen.tail hg ⟨hpg, hkk⟩) hy a hac
      have ha' := (mem_A C).mp ha
      rcases gate_eq C hC g hpg.1 hpg.2.1 with hand | hor
      · rw [hand] at ha'
        rw [hand y] at hyg
        rw [Bool.and_eq_true] at ha'
        rcases Bool.and_eq_false_iff.mp hyg with h0 | h1
        · exact child 0 (Or.inl rfl) h0 ((mem_A C).mpr ha'.1)
        · exact child 1 (Or.inr rfl) h1 ((mem_A C).mpr ha'.2)
      · rw [hor] at ha'
        rw [hor y] at hyg
        rw [Bool.or_eq_true] at ha'
        rw [Bool.or_eq_false_iff] at hyg
        rcases ha' with h0 | h1
        · exact child 0 (Or.inl rfl) hyg.1 ((mem_A C).mpr h0)
        · exact child 1 (Or.inr rfl) hyg.2 ((mem_A C).mpr h1)
    · have hgX : g ∈ X := (memX g).mpr ⟨Nat.lt_succ_of_le (hreach_le g hg), hg, hpg⟩
      refine ⟨g, hgX, ?_, ha⟩
      by_cases hgn : g < n
      · exact A_card_input C g hgn
      · by_cases hgN : n + C.gates.length ≤ g
        · exact A_card_ge C g hgN
        · by_cases hs : A n C g ⊆ Si
          · by_contra hc
            push_neg at hc
            exact hpg ⟨by omega, by omega, hs, hc⟩
          · have hgXL : g ∈ XL := (memXL g).mpr ⟨hgX, hs⟩
            have h3 := hy3 g hgXL
            rw [hyg] at h3
            exact absurd h3 (by decide)
  obtain ⟨Xs, hXsdef⟩ : ∃ Xs : Finset ℕ, Xs = X.filter (fun r => (A n C r).card ≤ 1) := ⟨_, rfl⟩
  have hsub3 : A n C o ⊆ Xs.biUnion (fun r => A n C r) := by
    intro a ha
    obtain ⟨r, hr, hc, har⟩ := walk o Relation.ReflTransGen.refl hyo a ha
    exact Finset.mem_biUnion.mpr ⟨r, by rw [hXsdef, Finset.mem_filter]; exact ⟨hr, hc⟩, har⟩
  have hb1 := (Finset.card_le_card hsub3).trans Finset.card_biUnion_le
  have hb2 : ∑ r ∈ Xs, (A n C r).card ≤ Xs.card := by
    calc ∑ r ∈ Xs, (A n C r).card ≤ ∑ _r ∈ Xs, 1 := by
          apply Finset.sum_le_sum
          intro r hr
          rw [hXsdef, Finset.mem_filter] at hr
          exact hr.2
      _ = Xs.card := by simp
  have hb3 : Xs.card ≤ X.card := by
    rw [hXsdef]
    exact Finset.card_filter_le _ _
  omega

end PEqualNP.Outside.L_meta_782

theorem PEqualNP.Outside.L_meta_782 : ∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true → p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → ∑ i : Fin m, c i ≤ C.size := by
  intro n m k S C o c hS h2 hC h4 h5 hck hcA
  have hper : ∀ i : Fin m, ∃ P : Finset ℕ,
      (∀ r ∈ P, PEqualNP.Outside.L_meta_782.priv C (S i) r) ∧ c i ≤ P.card := by
    intro i
    exact PEqualNP.Outside.L_meta_782.per_output C hC (S i) (o i) k (c i) (h2 i)
      (fun a ha => h4 i a (Finset.mem_filter.mp ha).2) (fun x hx hz => h5 i x hx hz)
      (hck i) (hcA i)
  choose P hP hcP using hper
  have hdisj : ∀ i ∈ (Finset.univ : Finset (Fin m)), ∀ j ∈ (Finset.univ : Finset (Fin m)),
      i ≠ j → Disjoint (P i) (P j) := by
    intro i _ j _ hij
    rw [Finset.disjoint_left]
    intro r hri hrj
    obtain ⟨_, _, hsi, hci⟩ := hP i r hri
    obtain ⟨_, _, hsj, _⟩ := hP j r hrj
    have h1 := Finset.card_le_card (Finset.subset_inter hsi hsj)
    have h3 := hS i j hij
    omega
  calc ∑ i, c i ≤ ∑ i, (P i).card := Finset.sum_le_sum (fun i _ => hcP i)
    _ = (Finset.univ.biUnion P).card := (Finset.card_biUnion hdisj).symm
    _ ≤ (Finset.Ico n (n + C.gates.length)).card := by
        apply Finset.card_le_card
        intro r hr
        obtain ⟨i, _, hri⟩ := Finset.mem_biUnion.mp hr
        obtain ⟨h1, h3, _⟩ := hP i r hri
        rw [Finset.mem_Ico]
        exact ⟨h1, h3⟩
    _ = C.size := by simp [PEqualNP.CircuitLowerBounds.Circuit.size]
