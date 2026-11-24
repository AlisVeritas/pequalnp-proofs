import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1583_aux


theorem finite_set_has_cycle {N m : ℕ} (T : Finset (Fin N)) (hT : T.card = m)
    (hm : 0 < m) :
    ∃ sigma : Fin N → Fin N, (∀ x ∈ T, sigma x ∈ T) ∧ Set.InjOn sigma ↑T ∧
      (∀ x ∈ T, ∀ y ∈ T, ∃ k : ℕ, sigma^[k] x = y) := by
  classical
  letI : NeZero m := ⟨by omega⟩
  let e : T ≃ Fin m := Finset.equivFinOfCardEq hT
  let sigma : Fin N → Fin N := fun x =>
    if h : x ∈ T then (e.symm (finRotate m (e ⟨x,h⟩))).val else x
  have hs (x : Fin N) (hx : x ∈ T) :
      sigma x = (e.symm (finRotate m (e ⟨x,hx⟩))).val := by
    simp [sigma,hx]
  have hmem (x : Fin N) (hx : x ∈ T) : sigma x ∈ T := by
    rw [hs x hx]
    exact (e.symm _).property
  have hcode (x : Fin N) (hx : x ∈ T) :
      e ⟨sigma x,hmem x hx⟩ = finRotate m (e ⟨x,hx⟩) := by
    have he : (⟨sigma x,hmem x hx⟩ : T) = e.symm (finRotate m (e ⟨x,hx⟩)) :=
      Subtype.ext (hs x hx)
    rw [he]
    simp
  have hinj : Set.InjOn sigma ↑T := by
    intro x hx y hy hxy
    have he : e ⟨sigma x,hmem x hx⟩ = e ⟨sigma y,hmem y hy⟩ := by
      apply congrArg e
      exact Subtype.ext hxy
    rw [hcode x hx,hcode y hy] at he
    exact congrArg Subtype.val (e.injective ((finRotate m).injective he))
  have hiter (k : ℕ) (x : Fin N) (hx : x ∈ T) :
      ∃ hk : (sigma^[k] x) ∈ T,
        e ⟨sigma^[k] x,hk⟩ = (finRotate m)^[k] (e ⟨x,hx⟩) := by
    induction k with
    | zero => exact ⟨hx,rfl⟩
    | succ k ih =>
      obtain ⟨hk,hcodek⟩ := ih
      rw [Function.iterate_succ_apply']
      refine ⟨hmem _ hk, ?_⟩
      rw [hcode _ hk, hcodek, Function.iterate_succ_apply']
  refine ⟨sigma,hmem,hinj,?_⟩
  intro x hx y hy
  let k : Fin m := e ⟨y,hy⟩ - e ⟨x,hx⟩
  refine ⟨k.val,?_⟩
  obtain ⟨hk,he⟩ := hiter k.val x hx
  have hrot : (finRotate m)^[k.val] (e ⟨x,hx⟩) = e ⟨y,hy⟩ := by
    rw [← finCycle_eq_finRotate_iterate]
    simp [finCycle_apply,k,add_comm]
  rw [hrot] at he
  exact congrArg Subtype.val (e.injective he)




theorem cycle_no_short {N : ℕ} (T : Finset (Fin N)) (sigma : Fin N → Fin N)
    (hsize : 3 ≤ T.card)
    (hcycle : ∀ x ∈ T, ∀ y ∈ T, ∃ k : ℕ, sigma^[k] x = y) :
    ∀ x ∈ T, sigma x ≠ x ∧ sigma (sigma x) ≠ x := by
  intro x hx
  have htwo : sigma (sigma x) ≠ x := by
    intro h
    have horbit : ∀ k : ℕ, sigma^[k] x = x ∨ sigma^[k] x = sigma x := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [Function.iterate_succ_apply']
        rcases ih with ih | ih
        · exact Or.inr (by rw [ih])
        · exact Or.inl (by rw [ih, h])
    have hsub : T ⊆ ({x, sigma x} : Finset (Fin N)) := by
      intro y hy
      obtain ⟨k,hk⟩ := hcycle x hx y hy
      have ho := horbit k
      rw [hk] at ho
      simpa using ho
    have hc := Finset.card_le_card hsub
    have hc2 : ({x, sigma x} : Finset (Fin N)).card ≤ 2 := by
      calc
        _ ≤ ({sigma x} : Finset (Fin N)).card + 1 := Finset.card_insert_le _ _
        _ = 2 := by simp
    omega
  refine ⟨?_, htwo⟩
  intro hfix
  apply htwo
  rw [hfix, hfix]
theorem geometry (N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N))
    (hmeet : ∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1)
    (hT0 : T0 ⊆ L i0)
    (sigma : Fin N → Fin N) (x0 : Fin N) (B : Fin N → Fin N → Finset (Fin N))
    (hmap : ∀ x ∈ T0, sigma x ∈ T0)
    (hno : ∀ x ∈ T0, sigma x ≠ x ∧ sigma (sigma x) ≠ x)
    (hx0 : x0 ∈ T0)
    (hB1 : ∀ s : Fin N, s ≠ i0 → ∀ p ∈ L s, ∀ x ∈ T0, x ∈ L s →
      B s p = if p = x then (∅ : Finset (Fin N)) else {sigma x})
    (hB2 : ∀ s : Fin N, s ≠ i0 → ∀ r ∈ L i0 \ T0, r ∈ L s → ∀ p ∈ L s, B s p = {x0}) :
    (∀ s : Fin N, s ≠ i0 → ∀ p ∈ L s, B s p ∩ L s = ∅ ∧
      ((∃ v ∈ T0, (fun v : Fin N => decide (v = p ∨ v ∈ B s p)) v = true) ∨
        ∀ v : Fin N, v ∉ L i0 → (fun v : Fin N => decide (v = p ∨ v ∈ B s p)) v = true) ∧
      ∀ v ∈ L s, decide (v = p ∨ v ∈ B s p) = true ↔ v = p) ∧
    (∀ s s' : Fin N, s ≠ i0 → s' ≠ i0 → s ≠ s' → ¬
      ((∃ p ∈ L s \ L s', (B s p ∩ L s').Nonempty) ∧
       (∃ p ∈ L s' \ L s, (B s' p ∩ L s).Nonempty))) := by
  classical
  have uniq : ∀ s : Fin N, s ≠ i0 → ∀ u ∈ L s, u ∈ L i0 → ∀ u' ∈ L s, u' ∈ L i0 → u = u' := by
    intro s hs u hu hu0 u' hu' hu0'
    exact Finset.card_le_one.1 (hmeet s i0 hs).le u (Finset.mem_inter.2 ⟨hu,hu0⟩) u'
      (Finset.mem_inter.2 ⟨hu',hu0'⟩)
  have now : ∀ s : Fin N, s ≠ i0 → ∀ r ∈ L i0 \ T0, r ∈ L s → ∀ v ∈ T0, v ∉ L s := by
    intro s hs r hr hrs v hv hvs
    exact (Finset.mem_sdiff.mp hr).2 ((uniq s hs v hvs (hT0 hv) r hrs (Finset.mem_sdiff.mp hr).1) ▸ hv)
  have types : ∀ s : Fin N, s ≠ i0 → (∃ x ∈ T0, x ∈ L s) ∨ ∃ r ∈ L i0 \ T0, r ∈ L s := by
    intro s hs
    obtain ⟨z, hz⟩ := Finset.card_eq_one.1 (hmeet s i0 hs)
    have hzm : z ∈ L s ∩ L i0 := by rw [hz]; simp
    obtain ⟨hzs,hz0⟩ := Finset.mem_inter.mp hzm
    by_cases ht : z ∈ T0
    · exact Or.inl ⟨z,ht,hzs⟩
    · exact Or.inr ⟨z,Finset.mem_sdiff.mpr ⟨hz0,ht⟩,hzs⟩
  have memB : ∀ s : Fin N, s ≠ i0 → ∀ p ∈ L s, ∀ v ∈ B s p,
      v ∈ T0 ∧ v ∉ L s ∧ ((∃ x ∈ T0, x ∈ L s ∧ v = sigma x) ∨ ∃ r ∈ L i0 \ T0, r ∈ L s) := by
    intro s hs p hp v hv
    rcases types s hs with ⟨x,hx,hxs⟩ | ⟨r,hr,hrs⟩
    · rw [hB1 s hs p hp x hx hxs] at hv
      by_cases hpx : p = x
      · rw [if_pos hpx] at hv; simp at hv
      · rw [if_neg hpx, Finset.mem_singleton] at hv
        subst hv
        refine ⟨hmap x hx, fun hin => ?_, Or.inl ⟨x,hx,hxs,rfl⟩⟩
        exact (hno x hx).1 (uniq s hs _ hin (hT0 (hmap x hx)) x hxs (hT0 hx))
    · rw [hB2 s hs r hr hrs p hp, Finset.mem_singleton] at hv
      subst hv
      exact ⟨hx0, now s hs r hr hrs _ hx0, Or.inr ⟨r,hr,hrs⟩⟩
  constructor
  · intro s hs p hp
    have hd : B s p ∩ L s = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro v hv
      rw [Finset.mem_inter] at hv
      exact (memB s hs p hp v hv.1).2.1 hv.2
    refine ⟨hd, Or.inl ?_, ?_⟩
    · rcases types s hs with ⟨x,hx,hxs⟩ | ⟨r,hr,hrs⟩
      · by_cases hpx : p = x
        · exact ⟨x,hx, by simp [hpx]⟩
        · refine ⟨sigma x,hmap x hx,?_⟩
          rw [hB1 s hs p hp x hx hxs, if_neg hpx]; simp
      · refine ⟨x0,hx0,?_⟩
        rw [hB2 s hs r hr hrs p hp]; simp
    · intro v hv
      have hvB : v ∉ B s p := by
        intro h
        have h' : v ∈ B s p ∩ L s := Finset.mem_inter.mpr ⟨h,hv⟩
        rw [hd] at h'; simp at h'
      simp [hvB]
  · rintro s s' hs hs' hss ⟨⟨p,hp,v,hv⟩,⟨p',hp',v',hv'⟩⟩
    rw [Finset.mem_sdiff] at hp hp'
    rw [Finset.mem_inter] at hv hv'
    obtain ⟨hvT,_,hk⟩ := memB s hs p hp.1 v hv.1
    obtain ⟨hvT',_,hk'⟩ := memB s' hs' p' hp'.1 v' hv'.1
    rcases hk with ⟨x,hx,hxs,rfl⟩ | ⟨r,hr,hrs⟩
    · rcases hk' with ⟨x',hx',hxs',rfl⟩ | ⟨r',hr',hrs'⟩
      · have e1 : sigma x = x' := uniq s' hs' _ hv.2 (hT0 hvT) x' hxs' (hT0 hx')
        have e2 : sigma x' = x := uniq s hs _ hv'.2 (hT0 hvT') x hxs (hT0 hx)
        exact (hno x hx).2 (by rw [e1,e2])
      · exact now s' hs' r' hr' hrs' _ hvT hv.2
    · exact now s hs r hr hrs _ hvT' hv'.2

theorem geometry_from_cycle (N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N))
    (hmeet : ∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1)
    (hT0 : T0 ⊆ L i0) (hsize : 3 ≤ T0.card)
    (sigma : Fin N → Fin N) (x0 : Fin N) (B : Fin N → Fin N → Finset (Fin N))
    (hmap : ∀ x ∈ T0, sigma x ∈ T0)
    (hcycle : ∀ x ∈ T0, ∀ y ∈ T0, ∃ k : ℕ, sigma^[k] x = y)
    (hx0 : x0 ∈ T0)
    (hB1 : ∀ s : Fin N, s ≠ i0 → ∀ p ∈ L s, ∀ x ∈ T0, x ∈ L s →
      B s p = if p = x then (∅ : Finset (Fin N)) else {sigma x})
    (hB2 : ∀ s : Fin N, s ≠ i0 → ∀ r ∈ L i0 \ T0, r ∈ L s → ∀ p ∈ L s, B s p = {x0}) :
    (∀ s : Fin N, s ≠ i0 → ∀ p ∈ L s, B s p ∩ L s = ∅ ∧
      ((∃ v ∈ T0, (fun v : Fin N => decide (v = p ∨ v ∈ B s p)) v = true) ∨
        ∀ v : Fin N, v ∉ L i0 → (fun v : Fin N => decide (v = p ∨ v ∈ B s p)) v = true) ∧
      ∀ v ∈ L s, decide (v = p ∨ v ∈ B s p) = true ↔ v = p) ∧
    (∀ s s' : Fin N, s ≠ i0 → s' ≠ i0 → s ≠ s' → ¬
      ((∃ p ∈ L s \ L s', (B s p ∩ L s').Nonempty) ∧
       (∃ p ∈ L s' \ L s, (B s' p ∩ L s).Nonempty))) :=
  geometry N L i0 T0 hmeet hT0 sigma x0 B hmap (cycle_no_short T0 sigma hsize hcycle) hx0 hB1 hB2





end PEqualNP.Outside.L_meta_1583_aux

theorem PEqualNP.Outside.L_meta_1583 : ∀ (q m N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N)),
    3 ≤ q → 3 ≤ m → m ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    T0 ⊆ L i0 → T0.card = m →
    (∃ sigma : Fin N → Fin N, (∀ x ∈ T0, sigma x ∈ T0) ∧ Set.InjOn sigma ↑T0 ∧ (∀ x ∈ T0, ∀ y ∈ T0, ∃ k : ℕ, sigma^[k] x = y)) ∧
    ∀ (sigma : Fin N → Fin N) (x0 : Fin N) (B : Fin N → Fin N → Finset (Fin N)),
    (∀ x ∈ T0, sigma x ∈ T0) ∧ Set.InjOn sigma ↑T0 ∧ (∀ x ∈ T0, ∀ y ∈ T0, ∃ k : ℕ, sigma^[k] x = y) → x0 ∈ T0 →
    (∀ s : Fin N, s ≠ i0 → ∀ p ∈ L s, ∀ x ∈ T0, x ∈ L s → B s p = if p = x then (∅ : Finset (Fin N)) else {sigma x}) →
    (∀ s : Fin N, s ≠ i0 → ∀ r ∈ L i0 \ T0, r ∈ L s → ∀ p ∈ L s, B s p = {x0}) →
    (∀ s : Fin N, s ≠ i0 → ∀ p ∈ L s, B s p ∩ L s = ∅ ∧ ((∃ v ∈ T0, (fun v : Fin N => decide (v = p ∨ v ∈ B s p)) v = true) ∨ ∀ v : Fin N, v ∉ L i0 → (fun v : Fin N => decide (v = p ∨ v ∈ B s p)) v = true) ∧
      ∀ v ∈ L s, decide (v = p ∨ v ∈ B s p) = true ↔ v = p) ∧
    (∀ s s' : Fin N, s ≠ i0 → s' ≠ i0 → s ≠ s' → ¬ ((∃ p ∈ L s \ L s', (B s p ∩ L s').Nonempty) ∧ (∃ p ∈ L s' \ L s, (B s' p ∩ L s).Nonempty))) := by
  intro q m N L i0 T0 hq hm hmq hN hsizes hinter hcover hT hcard
  constructor
  · exact PEqualNP.Outside.L_meta_1583_aux.finite_set_has_cycle T0 hcard (by omega)
  · intro sigma x0 B hcycle hx0 hB1 hB2
    have hno : ∀ x ∈ T0, sigma x ≠ x ∧ sigma (sigma x) ≠ x :=
      PEqualNP.Outside.L_meta_1583_aux.cycle_no_short T0 sigma (by rw [hcard]; omega) hcycle.2.2
    exact PEqualNP.Outside.L_meta_1583_aux.geometry N L i0 T0 hinter hT sigma x0 B hcycle.1 hno hx0 hB1 hB2