import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_627

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem length_fold (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp [step]; omega

private theorem input_fold (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

/-- Preserve the meaning of an absent output selector after the eight new gates are appended. -/
private def selector (base i : ℕ) : ℕ := if i < base then i else base + 8

private def suffix (base u v o₁ o₂ : ℕ) : List Gate :=
  [⟨.or, [u, v]⟩, ⟨.and, [u, v]⟩, ⟨.not, [base + 1]⟩,
   ⟨.and, [base, base + 2]⟩, ⟨.not, [base + 3]⟩,
   ⟨.and, [base + 4, selector base o₁]⟩,
   ⟨.and, [base + 3, selector base o₂]⟩, ⟨.or, [base + 5, base + 6]⟩]

private theorem suffix_eval (w : List Bool) (u v o₁ o₂ : ℕ) (hu : u < w.length)
    (hv : v < w.length) :
    ((suffix w.length u v o₁ o₂).foldl step w).getD (w.length + 7) false =
      if w.getD u false = w.getD v false then w.getD o₁ false else w.getD o₂ false := by
  have old (t : List Bool) (i : ℕ) (hi : i < w.length) :
      (w ++ t).getD i false = w.getD i false := List.getD_append _ _ _ _ hi
  have fresh (t : List Bool) (i : ℕ) :
      (w ++ t).getD (w.length + i) false = t.getD i false := by
    rw [List.getD_append_right _ _ _ _ (by omega)]; simp
  have first (t : List Bool) : (w ++ t).getD w.length false = t.getD 0 false := by
    simpa using fresh t 0
  have safe (t : List Bool) (i : ℕ) (ht : t.length ≤ 8) :
      (w ++ t).getD (selector w.length i) false = w.getD i false := by
    unfold selector
    split_ifs with hi
    · exact old t i hi
    · rw [fresh, List.getD_eq_default _ _ ht, List.getD_eq_default _ _ (by omega)]
  simp only [suffix, List.foldl_cons, List.foldl_nil, step, List.map_cons,
    List.map_nil, GateOp.eval, List.all_cons, List.all_nil, List.any_cons, List.any_nil,
    List.headD_cons, id_eq, Bool.and_true, Bool.or_false, List.append_assoc, List.cons_append,
    List.nil_append, old _ u hu, old _ v hv, fresh, first, List.getD_cons_zero,
    List.getD_cons_succ]
  cases w.getD u false <;> cases w.getD v false <;> simp <;>
    simp only [← List.getD_eq_getElem?_getD] <;> apply safe <;> decide

theorem bound (n s : ℕ) (F : (Fin n → Bool) → Bool) (u v : Fin n)
    (h : ∃ C : Circuit, FanInTwo C ∧ C.size ≤ s ∧ ∃ o₁ o₂ : ℕ, ∀ x : Fin n → Bool,
      (C.wires (List.ofFn x)).getD o₁ false = F (Function.update x u (x v)) ∧
      (C.wires (List.ofFn x)).getD o₂ false = F (Function.update x u (!(x v)))) :
    HasCircuitSize n F (s + 8) := by
  obtain ⟨C, fan, budget, o₁, o₂, out⟩ := h
  let base := n + C.size
  let D : Circuit := ⟨C.gates ++ suffix base u.val v.val o₁ o₂, base + 7⟩
  refine ⟨D, ?_, ?_, ?_⟩
  · intro g hg
    change g ∈ C.gates ++ suffix base u.val v.val o₁ o₂ at hg
    rcases List.mem_append.mp hg with hOld | hNew
    · exact fan g hOld
    · simp only [suffix, List.mem_cons, List.not_mem_nil, or_false] at hNew
      rcases hNew with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · simp [D, Circuit.size, suffix] at budget ⊢
    omega
  · intro x
    let w := C.wires (List.ofFn x)
    have hw : w.length = base := by
      change (C.gates.foldl step (List.ofFn x)).length = n + C.gates.length
      rw [length_fold, List.length_ofFn]
    have primary (i : Fin n) : w.getD i.val false = x i := by
      change (C.gates.foldl step (List.ofFn x)).getD i.val false = x i
      rw [input_fold _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
      simp
    change ((C.gates ++ suffix base u.val v.val o₁ o₂).foldl step (List.ofFn x)).getD (base + 7) false = F x
    rw [List.foldl_append]
    change ((suffix base u.val v.val o₁ o₂).foldl step w).getD (base + 7) false = F x
    rw [← hw, suffix_eval _ _ _ _ _ (by rw [hw]; dsimp [base]; omega) (by rw [hw]; dsimp [base]; omega),
      primary, primary]
    obtain ⟨h₁, h₂⟩ := out x
    by_cases eq : x u = x v
    · rw [ite_eq_left eq, show w.getD o₁ false = _ from h₁, ← eq, Function.update_eq_self]
    · have ne : (!(x v)) = x u := by cases hu : x u <;> cases hv : x v <;> simp_all
      rw [ite_eq_right eq, show w.getD o₂ false = _ from h₂, ne, Function.update_eq_self]

end PEqualNP.Outside.L_meta_627

theorem PEqualNP.Outside.L_meta_627 :
    ∀ (n s : ℕ) (F : (Fin n → Bool) → Bool) (u v : Fin n),
      (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ s ∧
        ∃ o1 o2 : ℕ, ∀ x : Fin n → Bool,
          (C.wires (List.ofFn x)).getD o1 false = F (Function.update x u (x v)) ∧
          (C.wires (List.ofFn x)).getD o2 false = F (Function.update x u (!(x v)))) →
      PEqualNP.MetaComplexity.HasCircuitSize n F (s + 8) := PEqualNP.Outside.L_meta_627.bound
