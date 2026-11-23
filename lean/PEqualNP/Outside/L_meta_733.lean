import Mathlib.Combinatorics.SimpleGraph.Basic

theorem PEqualNP.Outside.L_meta_733 :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (X : Set (Fin n)),
      (∀ u v, G.Adj u v → (u ∈ X ↔ v ∉ X)) →
      ∀ I : Set (Fin n),
        ((∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v) ∧ (∀ v, v ∉ I → ∃ u ∈ I, G.Adj v u)) ↔
        ∃ B : Set (Fin n), (∀ b ∈ B, b ∉ X) ∧
          (∀ y, y ∉ X → ((∀ x, G.Adj y x → ∃ b ∈ B, G.Adj x b) ↔ y ∈ B)) ∧
          ∀ v, v ∈ I ↔ (v ∈ B ∨ (v ∈ X ∧ ∀ b ∈ B, ¬ G.Adj v b)) := by
  classical
  intro n G X cross I
  constructor
  · rintro ⟨indep, dom⟩
    let B : Set (Fin n) := I ∩ Xᶜ
    have inX (x : Fin n) (hx : x ∈ X) : x ∈ I ↔ ∀ b ∈ B, ¬ G.Adj x b := by
      constructor
      · intro hi b hb
        exact indep x hi b hb.1
      · intro none
        by_contra hn
        obtain ⟨b, hb, edge⟩ := dom x hn
        exact none b ⟨hb, (cross x b edge).mp hx⟩ edge
    refine ⟨B, fun _ hb => hb.2, ?_, ?_⟩
    · intro y hy
      constructor
      · intro cover
        refine ⟨?_, hy⟩
        by_contra hn
        obtain ⟨x, hx, edge⟩ := dom y hn
        obtain ⟨b, hb, adj⟩ := cover x edge
        exact indep x hx b hb.1 adj
      · intro hb x edge
        exact ⟨y, hb, edge.symm⟩
    · intro v
      constructor
      · intro hv
        by_cases hx : v ∈ X
        · exact Or.inr ⟨hx, (inX v hx).mp hv⟩
        · exact Or.inl ⟨hv, hx⟩
      · rintro (hb | ⟨hx, h⟩)
        · exact hb.1
        · exact (inX v hx).mpr h
  · rintro ⟨B, outside, sat, mem⟩
    constructor
    · intro u hu v hv edge
      rcases (mem u).mp hu with ub | ⟨ux, ufree⟩
      · rcases (mem v).mp hv with vb | ⟨_, vfree⟩
        · exact outside u ub ((cross u v edge).mpr (outside v vb))
        · exact vfree u ub edge.symm
      · rcases (mem v).mp hv with vb | ⟨vx, _⟩
        · exact ufree v vb edge
        · exact (cross u v edge).mp ux vx
    · intro v absent
      by_contra none
      apply absent
      apply (mem v).mpr
      by_cases vx : v ∈ X
      · exact Or.inr ⟨vx, fun b hb he => none ⟨b, (mem b).mpr (Or.inl hb), he⟩⟩
      · apply Or.inl
        apply (sat v vx).mp
        intro x edge
        have xx := (cross x v edge.symm).mpr vx
        by_contra missed
        exact none ⟨x, (mem x).mpr (Or.inr ⟨xx, fun b hb he => missed ⟨b, hb, he⟩⟩), edge⟩
