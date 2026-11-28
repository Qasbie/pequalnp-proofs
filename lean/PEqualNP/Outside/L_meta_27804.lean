import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_6158

namespace PEqualNP.Outside.L_meta_27804

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def runW (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma runW_nil (w : List Bool) : runW [] w = w := rfl

lemma runW_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    runW (g :: gs) w = runW gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

lemma runW_append (gs hs : List Gate) (w : List Bool) :
    runW (gs ++ hs) w = runW hs (runW gs w) := by
  simp [runW, List.foldl_append]

lemma runW_len (gs : List Gate) : ∀ w : List Bool, (runW gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [runW]
  | cons g gs ih => intro w; rw [runW_cons, ih]; simp; omega

lemma runW_old (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (runW gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [runW_cons, ih _ i (by simp; omega)]
    exact List.getD_append _ _ _ _ hi

lemma eval_eq_runW (C : Circuit) (w : List Bool) :
    C.eval w = (runW C.gates w).getD C.output false := rfl

lemma mono_eval_gate (g : Gate) (hg : g.op = .and ∨ g.op = .or) (u v : List Bool)
    (h : ∀ i, u.getD i false = true → v.getD i false = true) :
    g.op.eval (g.inputs.map fun i => u.getD i false) = true →
      g.op.eval (g.inputs.map fun i => v.getD i false) = true := by
  rcases hg with h1 | h1 <;> rw [h1] <;>
    simp only [GateOp.eval, List.all_eq_true, List.any_eq_true, List.mem_map, id_eq]
  · intro hu x ⟨i, hi, hx⟩; subst hx; exact h i (hu _ ⟨i, hi, rfl⟩)
  · rintro ⟨x, ⟨i, hi, rfl⟩, hx⟩; exact ⟨_, ⟨i, hi, rfl⟩, h i hx⟩

lemma runW_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) :
    ∀ (u v : List Bool), u.length = v.length →
      (∀ i, u.getD i false = true → v.getD i false = true) →
      ∀ i, (runW gs u).getD i false = true → (runW gs v).getD i false = true := by
  induction gs with
  | nil => intro u v _ h i; exact h i
  | cons g gs ih =>
    intro u v hl h i
    rw [runW_cons, runW_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) _ _ (by simp [hl])
    intro k hk
    rcases Nat.lt_trichotomy k u.length with hlt | heq | hgt
    · rw [List.getD_append _ _ _ _ hlt] at hk
      rw [List.getD_append _ _ _ _ (hl ▸ hlt)]
      exact h k hk
    · subst heq
      rw [List.getD_append_right _ _ _ _ (le_refl _)] at hk
      rw [hl, List.getD_append_right _ _ _ _ (le_refl _)]
      simp only [Nat.sub_self, List.getD_cons_zero] at hk ⊢
      exact mono_eval_gate g (hgs g (List.mem_cons_self ..)) u v h hk
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hk
      exact absurd hk (by simp)

lemma eval_mono (C : Circuit) (hm : Monotone2 C) (u v : List Bool) (hl : u.length = v.length)
    (h : ∀ i, u.getD i false = true → v.getD i false = true) :
    C.eval u = true → C.eval v = true :=
  runW_mono C.gates (fun g hg => by simpa using (hm g hg).1) u v hl h C.output

lemma eval_indep_of_unread (gs : List Gate) (w0 : ℕ) (hno : ∀ g ∈ gs, w0 ∉ g.inputs) :
    ∀ (u v : List Bool), u.length = v.length →
      (∀ i, i ≠ w0 → u.getD i false = v.getD i false) →
      ∀ i, i ≠ w0 → (runW gs u).getD i false = (runW gs v).getD i false := by
  induction gs with
  | nil => intro u v _ h i hi; exact h i hi
  | cons g gs ih =>
    intro u v hl h i hi
    have hno0 : w0 ∉ g.inputs := hno g (List.mem_cons_self ..)
    have heq : g.inputs.map (fun k => u.getD k false) = g.inputs.map (fun k => v.getD k false) :=
      List.map_congr_left (fun k hk => h k (fun e => hno0 (e ▸ hk)))
    rw [runW_cons, runW_cons, heq]
    apply ih (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg')) _ _ (by simp [hl])
    · intro k hk
      rcases Nat.lt_trichotomy k u.length with hlt | rfl | hgt
      · rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ (hl ▸ hlt)]; exact h k hk
      · rw [List.getD_append_right _ _ _ _ (le_refl _), hl,
            List.getD_append_right _ _ _ _ (le_refl _)]
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    · exact hi

def orChain (acc : ℕ) : List ℕ → List Gate
  | [] => []
  | w :: ws => ⟨.or, [acc, w]⟩ :: orChain (acc + 1) ws

lemma orChain_len (acc : ℕ) (ws : List ℕ) : (orChain acc ws).length = ws.length := by
  induction ws generalizing acc with
  | nil => rfl
  | cons w ws ih => simp [orChain, ih]

lemma orChain_mono (acc : ℕ) (ws : List ℕ) :
    ∀ g ∈ orChain acc ws, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction ws generalizing acc with
  | nil => intro g hg; simp [orChain] at hg
  | cons w ws ih =>
    intro g hg
    simp only [orChain, List.mem_cons] at hg
    rcases hg with rfl | hg
    · simp
    · exact ih _ g hg

lemma orChain_eval (ws : List ℕ) : ∀ (init : List Bool) (acc : ℕ),
    init.length = acc + 1 → (∀ w ∈ ws, w < acc) →
    (runW (orChain acc ws) init).getD (acc + ws.length) false =
      (init.getD acc false || ws.any (fun w => init.getD w false)) := by
  induction ws with
  | nil =>
    intro init acc _ _
    simp [orChain, runW]
  | cons w ws ih =>
    intro init acc hl hw
    have hw0 : w < acc := hw w (List.mem_cons_self ..)
    have hstep : (init ++ [GateOp.or.eval ([acc, w].map fun i => init.getD i false)]).length =
        (acc + 1) + 1 := by simp [hl]
    rw [orChain, runW_cons]
    have hidx : acc + (w :: ws).length = (acc + 1) + ws.length := by simp; omega
    rw [hidx, ih _ (acc + 1) hstep (fun x hx => by have := hw x (List.mem_cons_of_mem _ hx); omega)]
    have hlast : (init ++ [GateOp.or.eval ([acc, w].map fun i => init.getD i false)]).getD (acc + 1) false =
        (init.getD acc false || init.getD w false) := by
      have h1 : init.length = acc + 1 := hl
      rw [← h1, List.getD_append_right _ _ _ _ (le_refl _)]
      simp [GateOp.eval]
    have hany : ws.any (fun x => (init ++ [GateOp.or.eval ([acc, w].map fun i => init.getD i false)]).getD x false) =
        ws.any (fun x => init.getD x false) := by
      rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
      exact exists_congr fun x => and_congr_right fun hx => by
        have hx' := hw x (List.mem_cons_of_mem _ hx)
        rw [List.getD_append _ _ _ _ (by omega)]
    rw [hlast, hany]
    simp [Bool.or_assoc]

def extraWires (n m : ℕ) : List ℕ :=
  ((List.range (n - 3)).map (· + 3)) ++ ((List.range (m - 3)).map (· + (n + 3)))

lemma extraWires_len (n m : ℕ) : (extraWires n m).length = (n - 3) + (m - 3) := by
  simp [extraWires]

def upperGates (n m : ℕ) : List Gate :=
  let b := n + m
  [⟨.or, [0, n]⟩, ⟨.or, [1, n + 1]⟩, ⟨.or, [2, n + 2]⟩,
   ⟨.and, [b, b + 1]⟩, ⟨.or, [b, b + 1]⟩, ⟨.and, [b + 2, b + 4]⟩, ⟨.or, [b + 3, b + 5]⟩] ++
  orChain (b + 6) (extraWires n m)

def upperCirc (n m : ℕ) : Circuit :=
  ⟨upperGates n m, n + m + 6 + (extraWires n m).length⟩

lemma upperCirc_mono (n m : ℕ) : Monotone2 (upperCirc n m) := by
  intro g hg
  simp only [upperCirc, upperGates, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with (rfl | rfl | rfl | rfl | rfl | rfl | rfl) | hg
  · simp
  · simp
  · simp
  · simp
  · simp
  · simp
  · simp
  · exact orChain_mono _ _ g hg

lemma upperCirc_size (n m : ℕ) (hn : 4 ≤ n) (hm : 4 ≤ m) : (upperCirc n m).size ≤ n + m + 1 := by
  simp [upperCirc, upperGates, Circuit.size, orChain_len, extraWires_len]
  omega

lemma oneEach_len {n m : ℕ} (u : Fin n) (v : Fin m) : (oneEach u v).length = n + m := by
  simp [oneEach]

lemma oneEach_left {n m : ℕ} (u : Fin n) (v : Fin m) {i : ℕ} (hi : i < n) :
    (oneEach u v).getD i false = decide (i = u.val) := by
  simp only [oneEach]
  rw [List.getD_append _ _ _ _ (by simp [hi])]
  simp [List.getD_eq_getElem?_getD, hi, Fin.ext_iff, eq_comm]

lemma oneEach_right {n m : ℕ} (u : Fin n) (v : Fin m) {j : ℕ} (hj : j < m) :
    (oneEach u v).getD (n + j) false = decide (j = v.val) := by
  simp only [oneEach]
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD, hj, Fin.ext_iff, eq_comm]

lemma upperCirc_rep (n m : ℕ) (hn : 4 ≤ n) (hm : 4 ≤ m) :
    Represents (fun (u : Fin n) (v : Fin m) =>
      (64478 : ℕ).testBit (4 * min u.val 3 + min v.val 3)) (upperCirc n m) := by
  intro u v
  let inp := oneEach u v
  let b := n + m
  have hinp : inp.length = b := oneEach_len u v
  let baseGs : List Gate :=
    [⟨.or, [0, n]⟩, ⟨.or, [1, n + 1]⟩, ⟨.or, [2, n + 2]⟩,
     ⟨.and, [b, b + 1]⟩, ⟨.or, [b, b + 1]⟩, ⟨.and, [b + 2, b + 4]⟩, ⟨.or, [b + 3, b + 5]⟩]
  let wBase := runW baseGs inp
  have hwBaseLen : wBase.length = b + 6 + 1 := by
    have := runW_len baseGs inp
    simp [baseGs, hinp] at this
    omega
  rw [eval_eq_runW]
  change (runW (baseGs ++ orChain (b + 6) (extraWires n m)) inp).getD
      (b + 6 + (extraWires n m).length) false = _
  rw [runW_append]
  rw [orChain_eval (extraWires n m) wBase (b + 6) hwBaseLen (by
    intro w hw
    simp only [extraWires, List.mem_append, List.mem_map, List.mem_range] at hw
    rcases hw with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩ <;> omega)]
  have hold : ∀ i < b, wBase.getD i false = inp.getD i false := fun i hi =>
    runW_old baseGs inp i (by omega)
  have hextra : (extraWires n m).any (fun w => wBase.getD w false) = decide (3 ≤ u.val ∨ 3 ≤ v.val) := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, extraWires, List.mem_append, List.mem_map, List.mem_range,
      decide_eq_true_eq]
    constructor
    · rintro ⟨w, ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩, hw⟩
      · rw [hold (i + 3) (by omega), oneEach_left u v (by omega)] at hw
        simp only [decide_eq_true_eq] at hw; left; omega
      · rw [hold (j + (n + 3)) (by omega)] at hw
        have hidx : j + (n + 3) = n + (j + 3) := by omega
        rw [hidx, oneEach_right u v (by omega)] at hw
        simp only [decide_eq_true_eq] at hw; right; omega
    · rintro (hu | hv)
      · refine ⟨u.val, Or.inl ⟨u.val - 3, by omega, by omega⟩, ?_⟩
        rw [hold u.val (by omega), oneEach_left u v u.isLt]; simp
      · refine ⟨n + v.val, Or.inr ⟨v.val - 3, by omega, by omega⟩, ?_⟩
        rw [hold (n + v.val) (by omega), oneEach_right u v v.isLt]; simp
  have hbaseVal : wBase.getD (b + 6) false =
      (((inp.getD 0 false || inp.getD n false) && (inp.getD 1 false || inp.getD (n + 1) false)) ||
      ((inp.getD 2 false || inp.getD (n + 2) false) &&
        ((inp.getD 0 false || inp.getD n false) || (inp.getD 1 false || inp.getD (n + 1) false)))) := by
    have step (xs : List Bool) (e : Bool) (k : ℕ) (hk : xs.length = k) :
        (xs ++ [e]).getD k false = e := by subst hk; simp
    have old (xs : List Bool) (e : Bool) (i : ℕ) (hi : i < xs.length) :
        (xs ++ [e]).getD i false = xs.getD i false := List.getD_append _ _ _ _ hi
    let a0 := inp.getD 0 false || inp.getD n false
    let a1 := inp.getD 1 false || inp.getD (n + 1) false
    let a2 := inp.getD 2 false || inp.getD (n + 2) false
    let w1 := inp ++ [a0]
    let w2 := w1 ++ [a1]
    let w3 := w2 ++ [a2]
    let w4 := w3 ++ [a0 && a1]
    let w5 := w4 ++ [a0 || a1]
    let w6 := w5 ++ [a2 && (a0 || a1)]
    let w7 := w6 ++ [(a0 && a1) || (a2 && (a0 || a1))]
    have hw1 : runW [⟨.or, [0, n]⟩] inp = w1 := by simp [runW, GateOp.eval, w1, a0]
    have hw1l : w1.length = b + 1 := by simp [w1, hinp]
    have hw2 : runW [⟨.or, [1, n + 1]⟩] w1 = w2 := by
      simp only [runW_cons, runW_nil, GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
        List.any_nil, Bool.or_false, id_eq]
      rw [old _ _ 1 (by omega), old _ _ (n + 1) (by omega)]
    have hw2l : w2.length = b + 2 := by simp [w2, hw1l]
    have hw3 : runW [⟨.or, [2, n + 2]⟩] w2 = w3 := by
      simp only [runW_cons, runW_nil, GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
        List.any_nil, Bool.or_false, id_eq]
      rw [old _ _ 2 (by rw [hw1l]; omega), old _ _ 2 (by omega),
          old _ _ (n + 2) (by rw [hw1l]; omega), old _ _ (n + 2) (by omega)]
    have hw3l : w3.length = b + 3 := by simp [w3, hw2l]
    have hw3_b : w3.getD b false = a0 := by
      rw [old _ _ b (by rw [hw2l]; omega), old _ _ b (by rw [hw1l]; omega), step _ _ b hinp]
    have hw3_b1 : w3.getD (b + 1) false = a1 := by
      rw [old _ _ (b + 1) (by rw [hw2l]; omega), step _ _ (b + 1) hw1l]
    have hw3_b2 : w3.getD (b + 2) false = a2 := step _ _ (b + 2) hw2l
    have hw4 : runW [⟨.and, [b, b + 1]⟩] w3 = w4 := by
      simp only [runW_cons, runW_nil, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
        List.all_nil, Bool.and_true, id_eq, hw3_b, hw3_b1, w4]
    have hw4l : w4.length = b + 4 := by simp [w4, hw3l]
    have hw5 : runW [⟨.or, [b, b + 1]⟩] w4 = w5 := by
      simp only [runW_cons, runW_nil, GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
        List.any_nil, Bool.or_false, id_eq]
      rw [old _ _ b (by rw [hw3l]; omega), old _ _ (b + 1) (by rw [hw3l]; omega), hw3_b, hw3_b1]
    have hw5l : w5.length = b + 5 := by simp [w5, hw4l]
    have hw6 : runW [⟨.and, [b + 2, b + 4]⟩] w5 = w6 := by
      simp only [runW_cons, runW_nil, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
        List.all_nil, Bool.and_true, id_eq]
      rw [old _ _ (b + 2) (by rw [hw4l]; omega), old _ _ (b + 2) (by rw [hw3l]; omega),
          hw3_b2, step _ _ (b + 4) hw4l]
    have hw6l : w6.length = b + 6 := by simp [w6, hw5l]
    have hw7 : runW [⟨.or, [b + 3, b + 5]⟩] w6 = w7 := by
      simp only [runW_cons, runW_nil, GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
        List.any_nil, Bool.or_false, id_eq]
      rw [old _ _ (b + 3) (by rw [hw5l]; omega), old _ _ (b + 3) (by rw [hw4l]; omega),
          step _ _ (b + 3) hw3l, step _ _ (b + 5) hw5l]
    have hwb : wBase = w7 := by
      show runW baseGs inp = w7
      change runW ([⟨.or, [0, n]⟩] ++ [⟨.or, [1, n + 1]⟩] ++ [⟨.or, [2, n + 2]⟩] ++
        [⟨.and, [b, b + 1]⟩] ++ [⟨.or, [b, b + 1]⟩] ++ [⟨.and, [b + 2, b + 4]⟩] ++
        [⟨.or, [b + 3, b + 5]⟩]) inp = w7
      simp only [runW_append, hw1, hw2, hw3, hw4, hw5, hw6, hw7]
    rw [hwb]
    exact step _ _ (b + 6) hw6l
  have hl0 : inp.getD 0 false = decide (0 = u.val) := oneEach_left u v (i := 0) (by omega)
  have hl1 : inp.getD 1 false = decide (1 = u.val) := oneEach_left u v (i := 1) (by omega)
  have hl2 : inp.getD 2 false = decide (2 = u.val) := oneEach_left u v (i := 2) (by omega)
  have hr0 : inp.getD n false = decide (0 = v.val) := oneEach_right u v (j := 0) (by omega)
  have hr1 : inp.getD (n + 1) false = decide (1 = v.val) := oneEach_right u v (j := 1) (by omega)
  have hr2 : inp.getD (n + 2) false = decide (2 = v.val) := oneEach_right u v (j := 2) (by omega)
  rw [hextra, hbaseVal, hl0, hl1, hl2, hr0, hr1, hr2]
  dsimp only
  by_cases hu : u.val < 3
  · by_cases hv : v.val < 3
    · have hu' : min u.val 3 = u.val := Nat.min_eq_left (by omega)
      have hv' : min v.val 3 = v.val := Nat.min_eq_left (by omega)
      have hne : ¬ (3 ≤ u.val ∨ 3 ≤ v.val) := by omega
      rw [hu', hv', decide_eq_false hne, Bool.or_false]
      interval_cases u.val <;> interval_cases v.val <;> decide
    · have hv' : min v.val 3 = 3 := Nat.min_eq_right (by omega)
      have htr : 3 ≤ u.val ∨ 3 ≤ v.val := Or.inr (by omega)
      rw [hv', decide_eq_true htr, Bool.or_true]
      have hu' : min u.val 3 = u.val := Nat.min_eq_left (by omega)
      rw [hu']
      interval_cases u.val <;> decide
  · have hu' : min u.val 3 = 3 := Nat.min_eq_right (by omega)
    have htr : 3 ≤ u.val ∨ 3 ≤ v.val := Or.inl (by omega)
    rw [hu', decide_eq_true htr, Bool.or_true]
    have hmv : min v.val 3 ≤ 3 := Nat.min_le_right _ _
    generalize min v.val 3 = k at hmv ⊢
    interval_cases k <;> decide

abbrev Val := Sum Bool ℕ

def evalVal (w : List Bool) : Val → Bool
  | Sum.inl c => c
  | Sum.inr i => w.getD i false

def validVal (len : ℕ) : Val → Prop
  | Sum.inl _ => True
  | Sum.inr i => i < len

def simpAnd (newIdx : ℕ) : List Val → Option Gate × Val
  | [] => (none, Sum.inl true)
  | [s] => (none, s)
  | [Sum.inl false, _] => (none, Sum.inl false)
  | [_, Sum.inl false] => (none, Sum.inl false)
  | [Sum.inl true, s] => (none, s)
  | [s, Sum.inl true] => (none, s)
  | [Sum.inr a, Sum.inr b] => (some ⟨.and, [a, b]⟩, Sum.inr newIdx)
  | _ => (none, Sum.inl false)

def simpOr (newIdx : ℕ) : List Val → Option Gate × Val
  | [] => (none, Sum.inl false)
  | [s] => (none, s)
  | [Sum.inl true, _] => (none, Sum.inl true)
  | [_, Sum.inl true] => (none, Sum.inl true)
  | [Sum.inl false, s] => (none, s)
  | [s, Sum.inl false] => (none, s)
  | [Sum.inr a, Sum.inr b] => (some ⟨.or, [a, b]⟩, Sum.inr newIdx)
  | _ => (none, Sum.inl false)

def simpGate (op : GateOp) (newIdx : ℕ) (ins : List Val) : Option Gate × Val :=
  match op with
  | .and => simpAnd newIdx ins
  | .or => simpOr newIdx ins
  | _ => (none, Sum.inl false)

lemma simpAnd_mono (newIdx : ℕ) (ins : List Val) :
    ∀ g ∈ (simpAnd newIdx ins).1,
      g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  match ins with
  | [] => simp [simpAnd] at hg
  | [_] => simp [simpAnd] at hg
  | [Sum.inl false, _] => simp [simpAnd] at hg
  | [Sum.inl true, Sum.inl false] => simp [simpAnd] at hg
  | [Sum.inl true, Sum.inl true] => simp [simpAnd] at hg
  | [Sum.inl true, Sum.inr _] => simp [simpAnd] at hg
  | [Sum.inr _, Sum.inl false] => simp [simpAnd] at hg
  | [Sum.inr _, Sum.inl true] => simp [simpAnd] at hg
  | [Sum.inr _, Sum.inr _] => simp [simpAnd] at hg; subst hg; simp
  | _ :: _ :: _ :: _ => simp [simpAnd] at hg

lemma simpOr_mono (newIdx : ℕ) (ins : List Val) :
    ∀ g ∈ (simpOr newIdx ins).1,
      g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  match ins with
  | [] => simp [simpOr] at hg
  | [_] => simp [simpOr] at hg
  | [Sum.inl true, _] => simp [simpOr] at hg
  | [Sum.inl false, Sum.inl true] => simp [simpOr] at hg
  | [Sum.inl false, Sum.inl false] => simp [simpOr] at hg
  | [Sum.inl false, Sum.inr _] => simp [simpOr] at hg
  | [Sum.inr _, Sum.inl true] => simp [simpOr] at hg
  | [Sum.inr _, Sum.inl false] => simp [simpOr] at hg
  | [Sum.inr _, Sum.inr _] => simp [simpOr] at hg; subst hg; simp
  | _ :: _ :: _ :: _ => simp [simpOr] at hg

lemma simpGate_mono (op : GateOp) (newIdx : ℕ) (ins : List Val) :
    ∀ g ∈ (simpGate op newIdx ins).1,
      g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  cases op with
  | and => exact simpAnd_mono newIdx ins
  | or => exact simpOr_mono newIdx ins
  | not => intro g hg; simp [simpGate] at hg
  | mod _ => intro g hg; simp [simpGate] at hg
  | maj => intro g hg; simp [simpGate] at hg

lemma simpGate_none_of_const (op : GateOp) (newIdx : ℕ) (ins : List Val)
    (hop : op = .and ∨ op = .or) (hl : ins.length ≤ 2) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simpGate op newIdx ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl
  · match ins with
    | [] => simp at hc
    | [_] => rfl
    | [Sum.inl false, _] => rfl
    | [Sum.inl true, Sum.inl false] => rfl
    | [Sum.inl true, Sum.inl true] => rfl
    | [Sum.inl true, Sum.inr _] => rfl
    | [Sum.inr _, Sum.inl false] => rfl
    | [Sum.inr _, Sum.inl true] => rfl
    | [Sum.inr _, Sum.inr _] => simp at hc
    | _ :: _ :: _ :: _ => simp at hl
  · match ins with
    | [] => simp at hc
    | [_] => rfl
    | [Sum.inl true, _] => rfl
    | [Sum.inl false, Sum.inl true] => rfl
    | [Sum.inl false, Sum.inl false] => rfl
    | [Sum.inl false, Sum.inr _] => rfl
    | [Sum.inr _, Sum.inl true] => rfl
    | [Sum.inr _, Sum.inl false] => rfl
    | [Sum.inr _, Sum.inr _] => simp at hc
    | _ :: _ :: _ :: _ => simp at hl

lemma simpGate_eval (op : GateOp) (hop : op = .and ∨ op = .or)
    (w : List Bool) (ins : List Val) (hl : ins.length ≤ 2) (hv : ∀ s ∈ ins, validVal w.length s) :
    validVal (w.length + (simpGate op w.length ins).1.toList.length) (simpGate op w.length ins).2 ∧
    evalVal (runW (simpGate op w.length ins).1.toList w) (simpGate op w.length ins).2 =
      op.eval (ins.map (evalVal w)) := by
  rcases hop with rfl | rfl
  · match ins with
    | [] => simp [simpGate, simpAnd, evalVal, validVal, GateOp.eval]
    | [Sum.inl c] => simp [simpGate, simpAnd, evalVal, validVal, GateOp.eval]
    | [Sum.inr ia] =>
      have hia : ia < w.length := hv _ (List.mem_cons_self ..)
      simp [simpGate, simpAnd, evalVal, validVal, runW, GateOp.eval, hia]
    | [Sum.inl false, b] => cases b <;> simp_all [simpGate, simpAnd, evalVal, validVal, GateOp.eval]
    | [Sum.inl true, Sum.inl false] => simp [simpGate, simpAnd, evalVal, validVal, GateOp.eval]
    | [Sum.inl true, Sum.inl true] => simp [simpGate, simpAnd, evalVal, validVal, GateOp.eval]
    | [Sum.inl true, Sum.inr ib] =>
      have hib : ib < w.length := hv (Sum.inr ib) (by simp)
      simp [simpGate, simpAnd, evalVal, validVal, runW, GateOp.eval, hib]
    | [Sum.inr ia, Sum.inl false] => simp [simpGate, simpAnd, evalVal, validVal, GateOp.eval]
    | [Sum.inr ia, Sum.inl true] =>
      have hia : ia < w.length := hv (Sum.inr ia) (by simp)
      simp [simpGate, simpAnd, evalVal, validVal, runW, GateOp.eval, hia]
    | [Sum.inr ia, Sum.inr ib] =>
      refine ⟨by simp [simpGate, simpAnd, validVal], ?_⟩
      simp [simpGate, simpAnd, evalVal, runW, GateOp.eval]
    | _ :: _ :: _ :: _ => simp at hl
  · match ins with
    | [] => simp [simpGate, simpOr, evalVal, validVal, GateOp.eval]
    | [Sum.inl c] => simp [simpGate, simpOr, evalVal, validVal, GateOp.eval]
    | [Sum.inr ia] =>
      have hia : ia < w.length := hv _ (List.mem_cons_self ..)
      simp [simpGate, simpOr, evalVal, validVal, runW, GateOp.eval, hia]
    | [Sum.inl true, b] => cases b <;> simp_all [simpGate, simpOr, evalVal, validVal, GateOp.eval]
    | [Sum.inl false, Sum.inl true] => simp [simpGate, simpOr, evalVal, validVal, GateOp.eval]
    | [Sum.inl false, Sum.inl false] => simp [simpGate, simpOr, evalVal, validVal, GateOp.eval]
    | [Sum.inl false, Sum.inr ib] =>
      have hib : ib < w.length := hv (Sum.inr ib) (by simp)
      simp [simpGate, simpOr, evalVal, validVal, runW, GateOp.eval, hib]
    | [Sum.inr ia, Sum.inl true] => simp [simpGate, simpOr, evalVal, validVal, GateOp.eval]
    | [Sum.inr ia, Sum.inl false] =>
      have hia : ia < w.length := hv (Sum.inr ia) (by simp)
      simp [simpGate, simpOr, evalVal, validVal, runW, GateOp.eval, hia]
    | [Sum.inr ia, Sum.inr ib] =>
      refine ⟨by simp [simpGate, simpOr, validVal], ?_⟩
      simp [simpGate, simpOr, evalVal, runW, GateOp.eval]
    | _ :: _ :: _ :: _ => simp at hl

def compile (gs : List Gate) (env : List Val) (newLen : ℕ) : List Gate × List Val :=
  match gs with
  | [] => ([], env)
  | g :: rest =>
    let ins := g.inputs.map (fun i => if i < env.length then env.getD i (Sum.inl false) else Sum.inl false)
    let r := simpGate g.op newLen ins
    let gs1 := r.1.toList
    let p := compile rest (env ++ [r.2]) (newLen + gs1.length)
    (gs1 ++ p.1, p.2)

lemma compile_mono (gs : List Gate) : ∀ (env : List Val) (newLen : ℕ) (g : Gate),
    g ∈ (compile gs env newLen).1 →
      g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction gs with
  | nil => intro _ _ g hg; simp [compile] at hg
  | cons g0 rest ih =>
    intro env newLen g hg
    simp only [compile, List.mem_append] at hg
    rcases hg with h1 | h2
    · exact simpGate_mono _ _ _ g (Option.mem_toList.mp h1)
    · exact ih _ _ g h2

lemma compile_len_le (gs : List Gate) : ∀ (env : List Val) (newLen : ℕ),
    (compile gs env newLen).1.length ≤ gs.length := by
  induction gs with
  | nil => intro _ _; simp [compile]
  | cons g0 rest ih =>
    intro env newLen
    simp only [compile, List.length_append, List.length_cons]
    let ins := g0.inputs.map (fun i => if i < env.length then env.getD i (Sum.inl false) else Sum.inl false)
    let r := simpGate g0.op newLen ins
    have h1 : r.1.toList.length ≤ 1 := by cases r.1 <;> simp
    have h2 := ih (env ++ [r.2]) (newLen + r.1.toList.length)
    change r.1.toList.length + (compile rest (env ++ [r.2]) (newLen + r.1.toList.length)).1.length ≤ rest.length + 1
    omega

lemma compile_len_lt (gs : List Gate) (w0 : ℕ)
    (hm : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (hmem : ∃ g ∈ gs, w0 ∈ g.inputs) :
    ∀ (env : List Val) (newLen : ℕ), w0 < env.length →
      env.getD w0 (Sum.inl false) = Sum.inl false →
      (compile gs env newLen).1.length + 1 ≤ gs.length := by
  induction gs with
  | nil => rcases hmem with ⟨g, hg, _⟩; simp at hg
  | cons g0 rest ih =>
    intro env newLen hw0 henv
    simp only [compile, List.length_append, List.length_cons]
    have hg0 := hm g0 (List.mem_cons_self ..)
    let ins := g0.inputs.map (fun i => if i < env.length then env.getD i (Sum.inl false) else Sum.inl false)
    let r := simpGate g0.op newLen ins
    change r.1.toList.length + (compile rest (env ++ [r.2]) (newLen + r.1.toList.length)).1.length + 1 ≤ rest.length + 1
    by_cases h0 : w0 ∈ g0.inputs
    · have hnone : r.1 = none := by
        apply simpGate_none_of_const g0.op newLen ins hg0.1 (by simp [ins, hg0.2])
        refine ⟨false, List.mem_map.mpr ⟨w0, h0, ?_⟩⟩
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hw0, Option.getD_some] at henv
        simp [hw0, henv]
      have hlen0 : r.1.toList.length = 0 := by rw [hnone]; rfl
      have hrest := compile_len_le rest (env ++ [r.2]) (newLen + r.1.toList.length)
      omega
    · have hmem' : ∃ g ∈ rest, w0 ∈ g.inputs := by
        rcases hmem with ⟨g, hg, hw⟩
        rcases List.mem_cons.mp hg with rfl | hg
        · exact absurd hw h0
        · exact ⟨g, hg, hw⟩
      have h1 : r.1.toList.length ≤ 1 := by cases r.1 <;> simp
      have h2 := ih (fun g hg => hm g (List.mem_cons_of_mem _ hg)) hmem'
        (env ++ [r.2]) (newLen + r.1.toList.length)
        (by simp; omega) (by rw [List.getD_append _ _ _ _ hw0]; exact henv)
      omega

lemma compile_eval (gs : List Gate) (hm : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) :
    ∀ (env : List Val) (wOld wNew : List Bool),
      env.length = wOld.length →
      (∀ s ∈ env, validVal wNew.length s) →
      (∀ i < wOld.length, evalVal wNew (env.getD i (Sum.inl false)) = wOld.getD i false) →
      (compile gs env wNew.length).2.length = (runW gs wOld).length ∧
      (∀ i < (runW gs wOld).length,
        evalVal (runW (compile gs env wNew.length).1 wNew)
          ((compile gs env wNew.length).2.getD i (Sum.inl false)) =
        (runW gs wOld).getD i false) := by
  induction gs with
  | nil =>
    intro env wOld wNew hl _ hev
    exact ⟨hl, hev⟩
  | cons g0 rest ih =>
    intro env wOld wNew hl hval hev
    have hg0 := hm g0 (List.mem_cons_self ..)
    let ins := g0.inputs.map (fun i => if i < env.length then env.getD i (Sum.inl false) else Sum.inl false)
    let r := simpGate g0.op wNew.length ins
    let gs1 := r.1.toList
    have hinsVal : ∀ s ∈ ins, validVal wNew.length s := by
      intro s hs
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hs
      by_cases hi : i < env.length
      · rw [ite_eq_left hi]
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
        exact hval _ (List.getElem_mem hi)
      · rw [ite_eq_right hi]; trivial
    have hstep := simpGate_eval g0.op hg0.1 wNew ins (by simp [ins, hg0.2]) hinsVal
    have hmap : ins.map (evalVal wNew) = g0.inputs.map (fun i => wOld.getD i false) := by
      simp only [ins, List.map_map]
      apply List.map_congr_left
      intro i _
      simp only [Function.comp_apply]
      by_cases hi : i < env.length
      · rw [ite_eq_left hi]; exact hev i (by omega)
      · rw [ite_eq_right hi, List.getD_eq_default _ _ (by omega)]; rfl
    have hnewLen : (runW gs1 wNew).length = wNew.length + gs1.length := runW_len gs1 wNew
    have ihRes := ih (fun g hg => hm g (List.mem_cons_of_mem _ hg))
      (env ++ [r.2])
      (wOld ++ [g0.op.eval (g0.inputs.map fun i => wOld.getD i false)])
      (runW gs1 wNew)
      (by simp [hl])
      (by
        intro s hs
        rw [List.mem_append, List.mem_singleton] at hs
        rcases hs with hs | rfl
        · cases s with
          | inl _ => trivial
          | inr idx =>
            have hlt : idx < wNew.length := hval _ hs
            change idx < (runW gs1 wNew).length
            omega
        · rw [hnewLen]; exact hstep.1)
      (by
        intro i hi
        simp only [List.length_append, List.length_singleton] at hi
        by_cases hlt : i < wOld.length
        · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ hlt]
          have hvi : validVal wNew.length (env.getD i (Sum.inl false)) := by
            have hi' : i < env.length := by omega
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
            exact hval _ (List.getElem_mem hi')
          have hold : evalVal (runW gs1 wNew) (env.getD i (Sum.inl false)) =
              evalVal wNew (env.getD i (Sum.inl false)) := by
            cases he : env.getD i (Sum.inl false) with
            | inl _ => rfl
            | inr idx =>
              rw [he] at hvi
              exact runW_old gs1 wNew idx hvi
          rw [hold, hev i hlt]
        · have heq : i = wOld.length := by omega
          subst heq
          rw [← hl, List.getD_append_right _ _ _ _ (le_refl _),
              hl, List.getD_append_right _ _ _ _ (le_refl _)]
          simp only [Nat.sub_self, List.getD_cons_zero]
          rw [hstep.2, hmap])
    simp only [compile, runW_cons, runW_append]
    have e1 : wNew.length + gs1.length = (runW gs1 wNew).length := hnewLen.symm
    simpa only [ins, r, gs1, e1] using ihRes

def setFalse (xs : List Bool) (w0 : ℕ) : List Bool :=
  xs.mapIdx (fun i b => if i = w0 then false else b)

lemma setFalse_len (xs : List Bool) (w0 : ℕ) : (setFalse xs w0).length = xs.length := by
  simp [setFalse]

lemma setFalse_getD (xs : List Bool) (w0 i : ℕ) :
    (setFalse xs w0).getD i false = if i = w0 then false else xs.getD i false := by
  by_cases hi : i < xs.length
  · simp [setFalse, List.getD_eq_getElem?_getD, hi]
  · have hle : xs.length ≤ i := by omega
    rw [List.getD_eq_default _ _ (by rw [setFalse_len]; exact hle),
        List.getD_eq_default _ _ hle]
    simp

lemma kill_one (N : ℕ) (C : Circuit) (hm : Monotone2 C) (w0 : ℕ) (hw0 : w0 < N)
    (hread : ∃ g ∈ C.gates, w0 ∈ g.inputs)
    (hzero : ∃ x : List Bool, x.length = N ∧ C.eval (setFalse x w0) = false) :
    ∃ C' : Circuit, Monotone2 C' ∧ C'.size + 1 ≤ C.size ∧
      ∀ x : List Bool, x.length = N → C'.eval x = C.eval (setFalse x w0) := by
  let env0 : List Val := (List.range N).map (fun i => if i = w0 then Sum.inl false else Sum.inr i)
  have henv0Len : env0.length = N := by simp [env0]
  have henv0w0 : env0.getD w0 (Sum.inl false) = Sum.inl false := by
    simp [env0, List.getD_eq_getElem?_getD, hw0]
  have hm' : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 :=
    fun g hg => ⟨by simpa using (hm g hg).1, (hm g hg).2⟩
  let res := compile C.gates env0 N
  have hlen : res.1.length + 1 ≤ C.gates.length :=
    compile_len_lt C.gates w0 hm' hread env0 N (by omega) henv0w0
  have hmono : ∀ g ∈ res.1, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 :=
    compile_mono C.gates env0 N
  have hevalAll : ∀ x : List Bool, x.length = N →
      res.2.length = (runW C.gates (setFalse x w0)).length ∧
      ∀ i < (runW C.gates (setFalse x w0)).length,
        evalVal (runW res.1 x) (res.2.getD i (Sum.inl false)) =
          (runW C.gates (setFalse x w0)).getD i false := by
    intro x hx
    have hcomp := compile_eval C.gates hm' env0 (setFalse x w0) x
      (by rw [henv0Len, setFalse_len, hx])
      (by
        intro s hs
        simp only [env0, List.mem_map, List.mem_range] at hs
        obtain ⟨i, hi, rfl⟩ := hs
        by_cases h : i = w0
        · simp [h, validVal]
        · simp [h, validVal, hx, hi])
      (by
        intro i hi
        rw [setFalse_len, hx] at hi
        rw [setFalse_getD]
        simp only [env0, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
          Option.map_some, Option.getD_some]
        by_cases h : i = w0 <;> simp [h, evalVal])
    rw [hx] at hcomp
    exact hcomp
  by_cases hout : C.output < N + C.gates.length
  · cases ho : res.2.getD C.output (Sum.inl false) with
    | inl b =>
      cases b with
      | true =>
        exfalso
        obtain ⟨x, hx, hxf⟩ := hzero
        have h1 := (hevalAll x hx).2 C.output (by rw [runW_len, setFalse_len, hx]; exact hout)
        rw [ho] at h1
        rw [eval_eq_runW] at hxf
        simp only [evalVal] at h1
        rw [← h1] at hxf
        exact Bool.noConfusion hxf
      | false =>
        refine ⟨⟨res.1, N + res.1.length⟩, hmono, hlen, fun x hx => ?_⟩
        rw [eval_eq_runW, eval_eq_runW]
        have h1 := (hevalAll x hx).2 C.output (by rw [runW_len, setFalse_len, hx]; exact hout)
        rw [ho] at h1
        simp only [evalVal] at h1
        rw [← h1, List.getD_eq_default _ _ (by rw [runW_len, hx])]
    | inr o' =>
      refine ⟨⟨res.1, o'⟩, hmono, hlen, fun x hx => ?_⟩
      rw [eval_eq_runW, eval_eq_runW]
      have h1 := (hevalAll x hx).2 C.output (by rw [runW_len, setFalse_len, hx]; exact hout)
      rw [ho] at h1
      exact h1
  · refine ⟨⟨res.1, N + res.1.length⟩, hmono, hlen, fun x hx => ?_⟩
    rw [eval_eq_runW, eval_eq_runW]
    rw [List.getD_eq_default _ _ (by rw [runW_len, hx]),
        List.getD_eq_default _ _ (by rw [runW_len, setFalse_len, hx]; omega)]

def maskList (S : List ℕ) (xs : List Bool) : List Bool :=
  xs.mapIdx (fun i b => if i ∈ S then false else b)

lemma maskList_nil (xs : List Bool) : maskList [] xs = xs := by
  apply List.ext_getElem
  · simp [maskList]
  · intro i h1 h2; simp [maskList]

lemma maskList_cons (w : ℕ) (S : List ℕ) (xs : List Bool) :
    maskList (w :: S) xs = setFalse (maskList S xs) w := by
  apply List.ext_getElem
  · simp [maskList, setFalse]
  · intro i h1 h2
    simp only [maskList, setFalse, List.getElem_mapIdx, List.mem_cons]
    by_cases hw : i = w
    · simp [hw]
    · simp [hw]

lemma maskList_len (S : List ℕ) (xs : List Bool) : (maskList S xs).length = xs.length := by
  simp [maskList]

lemma maskList_getD (S : List ℕ) (xs : List Bool) (i : ℕ) :
    (maskList S xs).getD i false = if i ∈ S then false else xs.getD i false := by
  by_cases hi : i < xs.length
  · simp [maskList, List.getD_eq_getElem?_getD, hi]
  · have hle : xs.length ≤ i := by omega
    rw [List.getD_eq_default _ _ (by rw [maskList_len]; exact hle),
        List.getD_eq_default _ _ hle]
    simp

lemma kill_many (n m : ℕ) (hn : 4 ≤ n) (hm : 4 ≤ m)
    (A : Fin n → Fin m → Bool)
    (hA00 : A ⟨0, by omega⟩ ⟨0, by omega⟩ = false)
    (hA01 : A ⟨0, by omega⟩ ⟨1, by omega⟩ = true)
    (hA10 : A ⟨1, by omega⟩ ⟨0, by omega⟩ = true)
    (hAr0 : ∀ i : Fin n, 3 ≤ i.val → A i ⟨0, by omega⟩ = true)
    (hA0c : ∀ j : Fin m, 3 ≤ j.val → A ⟨0, by omega⟩ j = true) :
    ∀ (S : List ℕ), S.Nodup →
      (∀ w ∈ S, (3 ≤ w ∧ w < n) ∨ (n + 3 ≤ w ∧ w < n + m)) →
      ∀ (C : Circuit), Monotone2 C → Represents A C →
      ∃ C' : Circuit, Monotone2 C' ∧ C'.size + S.length ≤ C.size ∧
        ∀ x : List Bool, x.length = n + m → C'.eval x = C.eval (maskList S x) := by
  intro S
  induction S with
  | nil =>
    intro _ _ C hM _
    exact ⟨C, hM, by simp, fun x _ => by rw [maskList_nil]⟩
  | cons w0 rest ih =>
    intro hnd hS C hM hRep
    have hnd' : rest.Nodup := (List.nodup_cons.mp hnd).2
    have hw0not : w0 ∉ rest := (List.nodup_cons.mp hnd).1
    have hS' : ∀ w ∈ rest, (3 ≤ w ∧ w < n) ∨ (n + 3 ≤ w ∧ w < n + m) :=
      fun w hw => hS w (List.mem_cons_of_mem _ hw)
    obtain ⟨C1, hM1, hsz1, hev1⟩ := ih hnd' hS' C hM hRep
    let z0 : Fin n := ⟨0, by omega⟩
    let z1 : Fin n := ⟨1, by omega⟩
    let c0 : Fin m := ⟨0, by omega⟩
    let c1 : Fin m := ⟨1, by omega⟩
    have h00_mask : maskList rest (oneEach z0 c0) = oneEach z0 c0 := by
      apply List.ext_getElem (by rw [maskList_len])
      intro i h1 h2
      rw [maskList_len, oneEach_len] at h1
      have := maskList_getD rest (oneEach z0 c0) i
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (by rw [maskList_len, oneEach_len]; exact h1),
          List.getElem?_eq_getElem (by rw [oneEach_len]; exact h1)] at this
      simp only [Option.getD_some] at this
      rw [this]
      by_cases hi : i ∈ rest
      · simp only [hi, ite_true]
        rcases hS' i hi with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
        · have h := oneEach_left z0 c0 h2'
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [oneEach_len]; omega)] at h
          simp only [Option.getD_some] at h; rw [h]; simp [z0]; omega
        · have h := oneEach_right z0 c0 (j := i - n) (by omega)
          have hidx : n + (i - n) = i := by omega
          rw [hidx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [oneEach_len]; omega)] at h
          simp only [Option.getD_some] at h; rw [h]; simp [c0]; omega
      · simp [hi]
    have h00_mask2 : setFalse (oneEach z0 c0) w0 = oneEach z0 c0 := by
      apply List.ext_getElem (by rw [setFalse_len])
      intro i h1 h2
      have h := setFalse_getD (oneEach z0 c0) w0 i
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2] at h
      simp only [Option.getD_some] at h; rw [h]
      by_cases hi : i = w0
      · simp only [hi, ite_true]
        rcases hS w0 (List.mem_cons_self ..) with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
        · have h' := oneEach_left z0 c0 h2'
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hi ▸ h2)] at h'
          simp only [Option.getD_some] at h'; rw [h']; simp [z0]; omega
        · have h' := oneEach_right z0 c0 (j := w0 - n) (by omega)
          have hidx : n + (w0 - n) = w0 := by omega
          rw [hidx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hi ▸ h2)] at h'
          simp only [Option.getD_some] at h'; rw [h']; simp [c0]; omega
      · simp [hi]
    have hzero : ∃ x : List Bool, x.length = n + m ∧ C1.eval (setFalse x w0) = false := by
      refine ⟨oneEach z0 c0, oneEach_len _ _, ?_⟩
      rw [h00_mask2, hev1 _ (oneEach_len _ _), h00_mask, hRep, hA00]
    have hC1_00 : C1.eval (oneEach z0 c0) = false := by
      rw [hev1 _ (oneEach_len _ _), h00_mask, hRep, hA00]
    have hw0lt : w0 < n + m := by
      rcases hS w0 (List.mem_cons_self ..) with ⟨_, h2⟩ | ⟨_, h2⟩ <;> omega
    have hread : ∃ g ∈ C1.gates, w0 ∈ g.inputs := by
      by_contra hno
      push_neg at hno
      rcases hS w0 (List.mem_cons_self ..) with ⟨hw1, hw2⟩ | ⟨hw1, hw2⟩
      · let rw0 : Fin n := ⟨w0, hw2⟩
        have hw_mask : maskList rest (oneEach rw0 c0) = oneEach rw0 c0 := by
          apply List.ext_getElem (by rw [maskList_len])
          intro i h1 h2
          have h := maskList_getD rest (oneEach rw0 c0) i
          rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
              List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2] at h
          simp only [Option.getD_some] at h; rw [h]
          by_cases hi : i ∈ rest
          · simp only [hi, ite_true]
            have hne : i ≠ w0 := fun e => hw0not (e ▸ hi)
            rcases hS' i hi with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
            · have h' := oneEach_left rw0 c0 h2'
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2] at h'
              simp only [Option.getD_some] at h'; rw [h']; simp [rw0, hne]
            · have h' := oneEach_right rw0 c0 (j := i - n) (by omega)
              have hidx : n + (i - n) = i := by omega
              rw [hidx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2] at h'
              simp only [Option.getD_some] at h'; rw [h']; simp [c0]; omega
          · simp [hi]
        have hC1_r0 : C1.eval (oneEach rw0 c0) = true := by
          rw [hev1 _ (oneEach_len _ _), hw_mask, hRep, hAr0 rw0 hw1]
        by_cases hout : C1.output = w0
        · have h01_mask : maskList rest (oneEach z0 c1) = oneEach z0 c1 := by
            apply List.ext_getElem (by rw [maskList_len])
            intro i h1 h2
            have h := maskList_getD rest (oneEach z0 c1) i
            rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
                List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2] at h
            simp only [Option.getD_some] at h; rw [h]
            by_cases hi : i ∈ rest
            · simp only [hi, ite_true]
              rcases hS' i hi with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
              · have h' := oneEach_left z0 c1 h2'
                rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2] at h'
                simp only [Option.getD_some] at h'; rw [h']; simp [z0]; omega
              · have h' := oneEach_right z0 c1 (j := i - n) (by omega)
                have hidx : n + (i - n) = i := by omega
                rw [hidx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2] at h'
                simp only [Option.getD_some] at h'; rw [h']; simp [c1]; omega
            · simp [hi]
          have hC1_01 : C1.eval (oneEach z0 c1) = true := by
            rw [hev1 _ (oneEach_len _ _), h01_mask, hRep, hA01]
          rw [eval_eq_runW, hout, runW_old _ _ _ (by rw [oneEach_len]; exact hw0lt),
              oneEach_left _ _ hw2] at hC1_01
          simp only [decide_eq_true_eq, z0] at hC1_01
          omega
        · have heq := eval_indep_of_unread C1.gates w0 hno
            (oneEach rw0 c0) (setFalse (oneEach rw0 c0) w0)
            (by rw [setFalse_len])
            (fun i hi => by rw [setFalse_getD]; simp [hi])
            C1.output hout
          rw [← eval_eq_runW, ← eval_eq_runW, hC1_r0] at heq
          have hle : C1.eval (oneEach z0 c0) = true :=
            eval_mono C1 hM1 (setFalse (oneEach rw0 c0) w0) (oneEach z0 c0)
              (by rw [setFalse_len, oneEach_len, oneEach_len]) (fun i hi => by
              rw [setFalse_getD] at hi
              by_cases hw : i = w0
              · simp [hw] at hi
              · simp only [hw, ite_false] at hi
                by_cases hlt : i < n
                · rw [oneEach_left _ _ hlt] at hi; simp only [decide_eq_true_eq, rw0] at hi; exact absurd hi hw
                · by_cases hlt2 : i < n + m
                  · have hidx : n + (i - n) = i := by omega
                    rw [← hidx, oneEach_right _ _ (by omega)] at hi ⊢; exact hi
                  · rw [List.getD_eq_default _ _ (by rw [oneEach_len]; omega)] at hi; exact absurd hi (by simp))
              heq.symm
          rw [hC1_00] at hle; exact Bool.noConfusion hle
      · let c : Fin m := ⟨w0 - n, by omega⟩
        have hw_mask : maskList rest (oneEach z0 c) = oneEach z0 c := by
          apply List.ext_getElem (by rw [maskList_len])
          intro i h1 h2
          have h := maskList_getD rest (oneEach z0 c) i
          rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
              List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2] at h
          simp only [Option.getD_some] at h; rw [h]
          by_cases hi : i ∈ rest
          · simp only [hi, ite_true]
            have hne : i ≠ w0 := fun e => hw0not (e ▸ hi)
            rcases hS' i hi with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
            · have h' := oneEach_left z0 c h2'
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2] at h'
              simp only [Option.getD_some] at h'; rw [h']; simp [z0]; omega
            · have h' := oneEach_right z0 c (j := i - n) (by omega)
              have hidx : n + (i - n) = i := by omega
              rw [hidx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2] at h'
              simp only [Option.getD_some] at h'; rw [h']; simp [c]; omega
          · simp [hi]
        have hC1_0c : C1.eval (oneEach z0 c) = true := by
          rw [hev1 _ (oneEach_len _ _), hw_mask, hRep, hA0c c (by simp [c]; omega)]
        by_cases hout : C1.output = w0
        · have h10_mask : maskList rest (oneEach z1 c0) = oneEach z1 c0 := by
            apply List.ext_getElem (by rw [maskList_len])
            intro i h1 h2
            have h := maskList_getD rest (oneEach z1 c0) i
            rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
                List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2] at h
            simp only [Option.getD_some] at h; rw [h]
            by_cases hi : i ∈ rest
            · simp only [hi, ite_true]
              rcases hS' i hi with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
              · have h' := oneEach_left z1 c0 h2'
                rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2] at h'
                simp only [Option.getD_some] at h'; rw [h']; simp [z1]; omega
              · have h' := oneEach_right z1 c0 (j := i - n) (by omega)
                have hidx : n + (i - n) = i := by omega
                rw [hidx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2] at h'
                simp only [Option.getD_some] at h'; rw [h']; simp [c0]; omega
            · simp [hi]
          have hC1_10 : C1.eval (oneEach z1 c0) = true := by
            rw [hev1 _ (oneEach_len _ _), h10_mask, hRep, hA10]
          rw [eval_eq_runW, hout, runW_old _ _ _ (by rw [oneEach_len]; exact hw0lt)] at hC1_10
          have hidx : n + (w0 - n) = w0 := by omega
          rw [← hidx, oneEach_right _ _ (by omega)] at hC1_10
          simp only [decide_eq_true_eq, c0] at hC1_10
          omega
        · have heq := eval_indep_of_unread C1.gates w0 hno
            (oneEach z0 c) (setFalse (oneEach z0 c) w0)
            (by rw [setFalse_len])
            (fun i hi => by rw [setFalse_getD]; simp [hi])
            C1.output hout
          rw [← eval_eq_runW, ← eval_eq_runW, hC1_0c] at heq
          have hle : C1.eval (oneEach z0 c0) = true :=
            eval_mono C1 hM1 (setFalse (oneEach z0 c) w0) (oneEach z0 c0)
              (by rw [setFalse_len, oneEach_len, oneEach_len]) (fun i hi => by
              rw [setFalse_getD] at hi
              by_cases hw : i = w0
              · simp [hw] at hi
              · simp only [hw, ite_false] at hi
                by_cases hlt : i < n
                · rw [oneEach_left _ _ hlt] at hi ⊢; exact hi
                · by_cases hlt2 : i < n + m
                  · have hidx : n + (i - n) = i := by omega
                    rw [← hidx, oneEach_right _ _ (by omega)] at hi
                    simp only [decide_eq_true_eq, c] at hi; omega
                  · rw [List.getD_eq_default _ _ (by rw [oneEach_len]; omega)] at hi; exact absurd hi (by simp))
              heq.symm
          rw [hC1_00] at hle; exact Bool.noConfusion hle
    obtain ⟨C2, hM2, hsz2, hev2⟩ := kill_one (n + m) C1 hM1 w0 hw0lt hread hzero
    refine ⟨C2, hM2, by simp; omega, fun x hx => ?_⟩
    rw [hev2 x hx, hev1 _ (by rw [setFalse_len]; exact hx), maskList_cons]
    have hcomm : maskList rest (setFalse x w0) = setFalse (maskList rest x) w0 := by
      apply List.ext_getElem (by simp [maskList, setFalse])
      intro i h1 h2
      simp only [maskList, setFalse, List.getElem_mapIdx]
      by_cases hw : i = w0 <;> by_cases hr : i ∈ rest <;> simp [hw, hr]
    rw [hcomm]

def liftTo4 (n m : ℕ) (u v : Fin 4) (hn : 4 ≤ n) (hm : 4 ≤ m) : List Bool :=
  oneEach (⟨u.val, by omega⟩ : Fin n) (⟨v.val, by omega⟩ : Fin m)

lemma remap_to_8 (n m : ℕ) (hn : 4 ≤ n) (hm : 4 ≤ m) (C : Circuit) (hM : Monotone2 C)
    (heval : ∀ (u v : Fin 4),
      C.eval (maskList (extraWires n m) (liftTo4 n m u v hn hm)) =
        (854 : ℕ).testBit (4 * u.val + v.val)) :
    RepSizeAtMost (fun u v : Fin 4 => (854 : ℕ).testBit (4 * u.val + v.val)) C.size := by
  let env0 : List Val := (List.range (n + m)).map (fun i =>
    if i < 3 then Sum.inr i
    else if n ≤ i ∧ i < n + 3 then Sum.inr (4 + (i - n))
    else Sum.inl false)
  have hm' : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 :=
    fun g hg => ⟨by simpa using (hM g hg).1, (hM g hg).2⟩
  let res := compile C.gates env0 8
  have hlen : res.1.length ≤ C.gates.length := compile_len_le C.gates env0 8
  have hmono : ∀ g ∈ res.1, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 :=
    compile_mono C.gates env0 8
  have hev4 : ∀ (u v : Fin 4),
      res.2.length = (runW C.gates (maskList (extraWires n m) (liftTo4 n m u v hn hm))).length ∧
      ∀ i < (runW C.gates (maskList (extraWires n m) (liftTo4 n m u v hn hm))).length,
        evalVal (runW res.1 (oneEach u v)) (res.2.getD i (Sum.inl false)) =
          (runW C.gates (maskList (extraWires n m) (liftTo4 n m u v hn hm))).getD i false := by
    intro u v
    have hcomp := compile_eval C.gates hm' env0
      (maskList (extraWires n m) (liftTo4 n m u v hn hm)) (oneEach u v)
      (by simp [env0, maskList_len, liftTo4, oneEach_len])
      (by
        intro s hs
        simp only [env0, List.mem_map, List.mem_range] at hs
        obtain ⟨i, hi, rfl⟩ := hs
        rw [oneEach_len]
        split_ifs with h1 h2
        · change i < 4 + 4; omega
        · change 4 + (i - n) < 4 + 4; omega
        · trivial)
      (by
        intro i hi
        rw [maskList_len, liftTo4, oneEach_len] at hi
        rw [maskList_getD]
        have he : env0.getD i (Sum.inl false) =
            if i < 3 then Sum.inr i
            else if n ≤ i ∧ i < n + 3 then Sum.inr (4 + (i - n))
            else Sum.inl false := by
          simp only [env0, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
            Option.map_some, Option.getD_some]
        rw [he]
        by_cases h1 : i < 3
        · have hnot : i ∉ extraWires n m := by
            simp only [extraWires, List.mem_append, List.mem_map, List.mem_range]
            rintro (⟨a, _, ha⟩ | ⟨b, _, hb⟩) <;> omega
          simp only [h1, ite_true, hnot, ite_false, evalVal, liftTo4]
          rw [oneEach_left u v (by omega), oneEach_left _ _ (by omega)]
        · by_cases h2 : n ≤ i ∧ i < n + 3
          · have hnot : i ∉ extraWires n m := by
              simp only [extraWires, List.mem_append, List.mem_map, List.mem_range]
              rintro (⟨a, _, ha⟩ | ⟨b, _, hb⟩) <;> omega
            simp only [h1, h2, and_self, ite_true, ite_false, hnot, evalVal, liftTo4]
            have hidx : n + (i - n) = i := by omega
            rw [oneEach_right u v (j := i - n) (by omega), ← hidx, oneEach_right _ _ (by omega)]
            simp
          · have hin : i ∈ extraWires n m := by
              simp only [extraWires, List.mem_append, List.mem_map, List.mem_range]
              by_cases hlt : i < n
              · exact Or.inl ⟨i - 3, by omega, by omega⟩
              · exact Or.inr ⟨i - n - 3, by omega, by omega⟩
            simp only [h1, h2, ite_false, hin, ite_true, evalVal])
    rw [oneEach_len] at hcomp
    exact hcomp
  by_cases hout : C.output < n + m + C.gates.length
  · cases ho : res.2.getD C.output (Sum.inl false) with
    | inl b =>
      cases b with
      | true =>
        exfalso
        have h1 := (hev4 ⟨0, by omega⟩ ⟨0, by omega⟩).2 C.output
          (by rw [runW_len, maskList_len, liftTo4, oneEach_len]; exact hout)
        rw [ho] at h1
        have h2 := heval ⟨0, by omega⟩ ⟨0, by omega⟩
        rw [eval_eq_runW] at h2
        simp only [evalVal] at h1
        rw [← h1] at h2
        simp only [Fin.val_mk] at h2
        exact absurd h2 (by decide)
      | false =>
        refine ⟨⟨res.1, 8 + res.1.length⟩, hmono, hlen, fun u v => ?_⟩
        rw [eval_eq_runW]
        have h1 := (hev4 u v).2 C.output
          (by rw [runW_len, maskList_len, liftTo4, oneEach_len]; exact hout)
        rw [ho] at h1
        simp only [evalVal] at h1
        rw [List.getD_eq_default _ _ (by rw [runW_len, oneEach_len]), h1, ← eval_eq_runW, heval u v]
    | inr o' =>
      refine ⟨⟨res.1, o'⟩, hmono, hlen, fun u v => ?_⟩
      rw [eval_eq_runW]
      have h1 := (hev4 u v).2 C.output
        (by rw [runW_len, maskList_len, liftTo4, oneEach_len]; exact hout)
      rw [ho] at h1
      rw [show evalVal (runW res.1 (oneEach u v)) (Sum.inr o') =
            (runW res.1 (oneEach u v)).getD o' false from rfl] at h1
      rw [h1, ← eval_eq_runW, heval u v]
  · refine ⟨⟨res.1, 8 + res.1.length⟩, hmono, hlen, fun u v => ?_⟩
    rw [eval_eq_runW, List.getD_eq_default _ _ (by rw [runW_len, oneEach_len])]
    have h2 := heval u v
    rw [eval_eq_runW, List.getD_eq_default _ _ (by rw [runW_len, maskList_len, liftTo4, oneEach_len]; omega)] at h2
    exact h2

lemma maskList_idem (S : List ℕ) (xs : List Bool) : maskList S (maskList S xs) = maskList S xs := by
  apply List.ext_getElem (by simp [maskList])
  intro i h1 h2
  simp only [maskList, List.getElem_mapIdx]
  by_cases hi : i ∈ S <;> simp [hi]

theorem lower_bound (n m : ℕ) (hn : 4 ≤ n) (hm : 4 ≤ m) :
    ¬ RepSizeAtMost (fun (u : Fin n) (v : Fin m) =>
      (64478 : ℕ).testBit (4 * min u.val 3 + min v.val 3)) (n + m) := by
  intro ⟨C, hM, hsz, hRep⟩
  let A : Fin n → Fin m → Bool := fun u v => (64478 : ℕ).testBit (4 * min u.val 3 + min v.val 3)
  have hnd : (extraWires n m).Nodup := by
    unfold extraWires
    rw [List.nodup_append]
    refine ⟨(List.nodup_range (n := n - 3)).map (fun _ _ h => by omega),
      (List.nodup_range (n := m - 3)).map (fun _ _ h => by omega), ?_⟩
    intro a ha b hb
    simp only [List.mem_map, List.mem_range] at ha hb
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    omega
  have hmem : ∀ w ∈ extraWires n m, (3 ≤ w ∧ w < n) ∨ (n + 3 ≤ w ∧ w < n + m) := by
    intro w hw
    simp only [extraWires, List.mem_append, List.mem_map, List.mem_range] at hw
    rcases hw with ⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩
    · exact Or.inl ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
  have hA00 : A ⟨0, by omega⟩ ⟨0, by omega⟩ = false := by simp only [A]; decide
  have hA01 : A ⟨0, by omega⟩ ⟨1, by omega⟩ = true := by simp only [A]; decide
  have hA10 : A ⟨1, by omega⟩ ⟨0, by omega⟩ = true := by simp only [A]; decide
  have hAr0 : ∀ i : Fin n, 3 ≤ i.val → A i ⟨0, by omega⟩ = true := by
    intro i hi
    simp only [A, Nat.min_eq_right hi]
    decide
  have hA0c : ∀ j : Fin m, 3 ≤ j.val → A ⟨0, by omega⟩ j = true := by
    intro j hj
    simp only [A, Nat.min_eq_right hj]
    decide
  obtain ⟨C', hM', hsz', hev'⟩ := kill_many n m hn hm A hA00 hA01 hA10 hAr0 hA0c
    (extraWires n m) hnd hmem C hM hRep
  have hC'sz : C'.size ≤ 6 := by
    rw [extraWires_len] at hsz'
    omega
  have hev8 : ∀ (u v : Fin 4),
      C'.eval (maskList (extraWires n m) (liftTo4 n m u v hn hm)) =
        (854 : ℕ).testBit (4 * u.val + v.val) := by
    intro u v
    rw [hev' _ (by rw [maskList_len, liftTo4, oneEach_len]), maskList_idem]
    by_cases hu : u.val < 3
    · by_cases hv : v.val < 3
      · have hmask : maskList (extraWires n m) (liftTo4 n m u v hn hm) = liftTo4 n m u v hn hm := by
          apply List.ext_getElem (by rw [maskList_len])
          intro i h1 h2
          have h := maskList_getD (extraWires n m) (liftTo4 n m u v hn hm) i
          rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
              List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2] at h
          simp only [Option.getD_some] at h; rw [h]
          by_cases hi : i ∈ extraWires n m
          · simp only [hi, ite_true]
            dsimp only [liftTo4] at h2 ⊢
            rcases hmem i hi with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
            · have h' := oneEach_left (⟨u.val, by omega⟩ : Fin n) (⟨v.val, by omega⟩ : Fin m) h2'
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2] at h'
              simp only [Option.getD_some] at h'; rw [h']; simp; omega
            · have h' := oneEach_right (⟨u.val, by omega⟩ : Fin n) (⟨v.val, by omega⟩ : Fin m)
                (j := i - n) (by omega)
              have hidx : n + (i - n) = i := by omega
              rw [hidx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2] at h'
              simp only [Option.getD_some] at h'; rw [h']; simp; omega
          · simp [hi]
        rw [hmask, liftTo4, hRep]
        simp only [Nat.min_eq_left (show u.val ≤ 3 by omega),
          Nat.min_eq_left (show v.val ≤ 3 by omega)]
        interval_cases u.val <;> interval_cases v.val <;> decide
      · have hv3 : v.val = 3 := by omega
        have hbit : (854 : ℕ).testBit (4 * u.val + v.val) = false := by
          rw [hv3]; interval_cases u.val <;> decide
        rw [hbit]
        have hdiag : C.eval (oneEach (⟨u.val, by omega⟩ : Fin n) (⟨u.val, by omega⟩ : Fin m)) = false := by
          rw [hRep]
          simp only [Nat.min_eq_left (show u.val ≤ 3 by omega)]
          interval_cases u.val <;> decide
        cases hc : C.eval (maskList (extraWires n m) (liftTo4 n m u v hn hm)) with
        | false => rfl
        | true =>
          exfalso
          have hle := eval_mono C hM (maskList (extraWires n m) (liftTo4 n m u v hn hm))
            (oneEach (⟨u.val, by omega⟩ : Fin n) (⟨u.val, by omega⟩ : Fin m))
            (by rw [maskList_len, liftTo4, oneEach_len, oneEach_len])
            (fun i hi => by
              rw [maskList_getD] at hi
              by_cases hin : i ∈ extraWires n m
              · simp [hin] at hi
              · simp only [hin, ite_false, liftTo4] at hi
                by_cases hlt : i < n
                · rw [oneEach_left _ _ hlt] at hi ⊢; exact hi
                · by_cases hlt2 : i < n + m
                  · have hidx : n + (i - n) = i := by omega
                    rw [← hidx, oneEach_right _ _ (by omega)] at hi
                    simp only [decide_eq_true_eq] at hi
                    have : i ∈ extraWires n m := by
                      simp only [extraWires, List.mem_append, List.mem_map, List.mem_range]
                      exact Or.inr ⟨0, by omega, by omega⟩
                    exact absurd this hin
                  · rw [List.getD_eq_default _ _ (by rw [oneEach_len]; omega)] at hi
                    exact absurd hi (by simp))
            hc
          rw [hdiag] at hle; exact Bool.noConfusion hle
    · have hu3 : u.val = 3 := by omega
      have hbit : (854 : ℕ).testBit (4 * u.val + v.val) = false := by
        have hv4 : v.val < 4 := v.isLt
        rw [hu3]; interval_cases v.val <;> decide
      rw [hbit]
      by_cases hv : v.val < 3
      · have hdiag : C.eval (oneEach (⟨v.val, by omega⟩ : Fin n) (⟨v.val, by omega⟩ : Fin m)) = false := by
          rw [hRep]
          simp only [Nat.min_eq_left (show v.val ≤ 3 by omega)]
          interval_cases v.val <;> decide
        cases hc : C.eval (maskList (extraWires n m) (liftTo4 n m u v hn hm)) with
        | false => rfl
        | true =>
          exfalso
          have hle := eval_mono C hM (maskList (extraWires n m) (liftTo4 n m u v hn hm))
            (oneEach (⟨v.val, by omega⟩ : Fin n) (⟨v.val, by omega⟩ : Fin m))
            (by rw [maskList_len, liftTo4, oneEach_len, oneEach_len])
            (fun i hi => by
              rw [maskList_getD] at hi
              by_cases hin : i ∈ extraWires n m
              · simp [hin] at hi
              · simp only [hin, ite_false, liftTo4] at hi
                by_cases hlt : i < n
                · rw [oneEach_left _ _ hlt] at hi
                  simp only [decide_eq_true_eq] at hi
                  have : i ∈ extraWires n m := by
                    simp only [extraWires, List.mem_append, List.mem_map, List.mem_range]
                    exact Or.inl ⟨0, by omega, by omega⟩
                  exact absurd this hin
                · by_cases hlt2 : i < n + m
                  · have hidx : n + (i - n) = i := by omega
                    rw [← hidx, oneEach_right _ _ (by omega)] at hi ⊢; exact hi
                  · rw [List.getD_eq_default _ _ (by rw [oneEach_len]; omega)] at hi
                    exact absurd hi (by simp))
            hc
          rw [hdiag] at hle; exact Bool.noConfusion hle
      · have hv3 : v.val = 3 := by omega
        have hdiag : C.eval (oneEach (⟨0, by omega⟩ : Fin n) (⟨0, by omega⟩ : Fin m)) = false := by
          rw [hRep]; exact hA00
        cases hc : C.eval (maskList (extraWires n m) (liftTo4 n m u v hn hm)) with
        | false => rfl
        | true =>
          exfalso
          have hle := eval_mono C hM (maskList (extraWires n m) (liftTo4 n m u v hn hm))
            (oneEach (⟨0, by omega⟩ : Fin n) (⟨0, by omega⟩ : Fin m))
            (by rw [maskList_len, liftTo4, oneEach_len, oneEach_len])
            (fun i hi => by
              rw [maskList_getD] at hi
              by_cases hin : i ∈ extraWires n m
              · simp [hin] at hi
              · simp only [hin, ite_false, liftTo4] at hi
                by_cases hlt : i < n
                · rw [oneEach_left _ _ hlt] at hi
                  simp only [decide_eq_true_eq] at hi
                  have : i ∈ extraWires n m := by
                    simp only [extraWires, List.mem_append, List.mem_map, List.mem_range]
                    exact Or.inl ⟨0, by omega, by omega⟩
                  exact absurd this hin
                · by_cases hlt2 : i < n + m
                  · have hidx : n + (i - n) = i := by omega
                    rw [← hidx, oneEach_right _ _ (by omega)] at hi
                    simp only [decide_eq_true_eq] at hi
                    have : i ∈ extraWires n m := by
                      simp only [extraWires, List.mem_append, List.mem_map, List.mem_range]
                      exact Or.inr ⟨0, by omega, by omega⟩
                    exact absurd this hin
                  · rw [List.getD_eq_default _ _ (by rw [oneEach_len]; omega)] at hi
                    exact absurd hi (by simp))
            hc
          rw [hdiag] at hle; exact Bool.noConfusion hle
  obtain ⟨C8, hM8, hsz8, hRep8⟩ := remap_to_8 n m hn hm C' hM' hev8
  exact PEqualNP.Outside.L_meta_6158.2 ⟨C8, hM8, le_trans hsz8 hC'sz, hRep8⟩

end PEqualNP.Outside.L_meta_27804

theorem PEqualNP.Outside.L_meta_27804 : (∀ (n m : Nat), 4 ≤ n → 4 ≤ m →
    let A := fun (u : Fin n) (v : Fin m) =>
      (64478 : Nat).testBit (4 * min u.val 3 + min v.val 3)
    PEqualNP.Represents.RepSizeAtMost A (n + m + 1) ∧
      ¬ PEqualNP.Represents.RepSizeAtMost A (n + m)) := by
  intro n m hn hm
  exact ⟨⟨PEqualNP.Outside.L_meta_27804.upperCirc n m,
    PEqualNP.Outside.L_meta_27804.upperCirc_mono n m,
    PEqualNP.Outside.L_meta_27804.upperCirc_size n m hn hm,
    PEqualNP.Outside.L_meta_27804.upperCirc_rep n m hn hm⟩,
    PEqualNP.Outside.L_meta_27804.lower_bound n m hn hm⟩
