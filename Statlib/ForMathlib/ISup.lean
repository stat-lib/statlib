/-
Copyright (c) 2025 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

module

public import Mathlib.Data.EReal.Basic
public import Mathlib.Order.CompletePartialOrder

/-! # Lemmas about iSup and iInf
-/

@[expose] public section

lemma iSup₂_eq_sSup {α ι : Type*} [CompleteLattice ι] {P : α → Prop} {g : α → ι} :
    ⨆ (x : α) (_ : P x), g x = sSup {y | ∃ x, P x ∧ y = g x} := by
  rw [sSup_eq_iSup]
  simp_rw [Set.mem_ofPred_eq, iSup_exists, iSup_and]
  suffices ⨆ a, ⨆ x, ⨆ (_ : P x), ⨆ (_ : a = g x), a =
      ⨆ x, ⨆ (_ : P x), ⨆ a, ⨆ (_ : a = g x), a by
    simp_rw [this, iSup_iSup_eq_left]
  rw [iSup_comm]
  refine iSup_congr fun i => ?_
  rw [iSup_comm]

lemma iSup₃_eq_sSup {α ι : Type*} [CompleteLattice ι] {P₁ P₂ : α → Prop} {g : α → ι} :
    ⨆ (x : α) (_ : P₁ x) (_ : P₂ x), g x = sSup {y | ∃ x, P₁ x ∧ P₂ x ∧ y = g x} := by
  rw [sSup_eq_iSup]
  simp_rw [Set.mem_ofPred_eq, iSup_exists, iSup_and]
  suffices ⨆ a, ⨆ x, ⨆ (_ : P₁ x), ⨆ (_ : P₂ x), ⨆ (_ : a = g x), a =
      ⨆ x, ⨆ (_ : P₁ x), ⨆ (_ : P₂ x), ⨆ a, ⨆ (_ : a = g x), a by
    simp_rw [this, iSup_iSup_eq_left]
  rw [iSup_comm]
  refine iSup_congr fun i => ?_
  rw [iSup_comm]
  refine iSup_congr fun i => ?_
  rw [iSup_comm]

lemma iInf₂_eq_sInf {α ι : Type*} [CompleteLattice ι] {P : α → Prop} {g : α → ι} :
    ⨅ (x : α) (_ : P x), g x = sInf {y | ∃ x, P x ∧ y = g x} := by
  rw [sInf_eq_iInf]
  simp_rw [Set.mem_ofPred_eq, iInf_exists, iInf_and]
  suffices ⨅ a, ⨅ x, ⨅ (_ : P x), ⨅ (_ : a = g x), a =
      ⨅ x, ⨅ (_ : P x), ⨅ a, ⨅ (_ : a = g x), a by
    simp_rw [this, iInf_iInf_eq_left]
  rw [iInf_comm]
  refine iInf_congr fun i => ?_
  rw [iInf_comm]

lemma iInf₃_eq_sInf {α ι : Type*} [CompleteLattice ι] {P₁ P₂ : α → Prop} {g : α → ι} :
    ⨅ (x : α) (_ : P₁ x) (_ : P₂ x), g x = sInf {y | ∃ x, P₁ x ∧ P₂ x ∧ y = g x} := by
  rw [sInf_eq_iInf]
  simp_rw [Set.mem_ofPred_eq, iInf_exists, iInf_and]
  suffices ⨅ a, ⨅ x, ⨅ (_ : P₁ x), ⨅ (_ : P₂ x), ⨅ (_ : a = g x), a =
      ⨅ x, ⨅ (_ : P₁ x), ⨅ (_ : P₂ x), ⨅ a, ⨅ (_ : a = g x), a by
    simp_rw [this, iInf_iInf_eq_left]
  rw [iInf_comm]
  refine iInf_congr fun i => ?_
  rw [iInf_comm]
  refine iInf_congr fun i => ?_
  rw [iInf_comm]

lemma iInf₄_eq_sInf {α β ι : Type*} [CompleteLattice ι] {P₁ : α → Prop} {P₂ : β → Prop}
    {g : α → β → ι} :
    ⨅ (x : α) (y : β) (_ : P₁ x) (_ : P₂ y), g x y = sInf {z | ∃ x y, P₁ x ∧ P₂ y ∧ z = g x y} := by
  rw [sInf_eq_iInf]
  simp_rw [Set.mem_ofPred_eq, iInf_exists, iInf_and]
  suffices ⨅ a, ⨅ x, ⨅ y, ⨅ (_ : P₁ x), ⨅ (_ : P₂ y), ⨅ (_ : a = g x y), a =
      ⨅ x, ⨅ y, ⨅ (_ : P₁ x), ⨅ (_ : P₂ y), ⨅ a, ⨅ (_ : a = g x y), a by
    simp_rw [this, iInf_iInf_eq_left]
  rw [iInf_comm]
  refine iInf_congr fun i => ?_
  rw [iInf_comm]
  refine iInf_congr fun i => ?_
  rw [iInf_comm]
  refine iInf_congr fun i => ?_
  rw [iInf_comm]

lemma iSup₄_eq_sSup {α β ι : Type*} [CompleteLattice ι] {P₁ : α → Prop} {P₂ : β → Prop}
    {g : α → β → ι} :
    ⨆ (x : α) (y : β) (_ : P₁ x) (_ : P₂ y), g x y = sSup {z | ∃ x y, P₁ x ∧ P₂ y ∧ z = g x y} := by
  rw [sSup_eq_iSup]
  simp_rw [Set.mem_ofPred_eq, iSup_exists, iSup_and]
  suffices ⨆ a, ⨆ x, ⨆ y, ⨆ (_ : P₁ x), ⨆ (_ : P₂ y), ⨆ (_ : a = g x y), a =
      ⨆ x, ⨆ y, ⨆ (_ : P₁ x), ⨆ (_ : P₂ y), ⨆ a, ⨆ (_ : a = g x y), a by
    simp_rw [this, iSup_iSup_eq_left]
  rw [iSup_comm]
  refine iSup_congr fun i => ?_
  rw [iSup_comm]
  refine iSup_congr fun i => ?_
  rw [iSup_comm]
  refine iSup_congr fun i => ?_
  rw [iSup_comm]

open Pointwise

lemma sInf_add' {α : Type*} [AddCommMagma α] [Sub α] [CompleteLattice α] [OrderedSub α]
    {s t : Set α} : sInf (s + t) = sInf s + sInf t := by
  let u := fun (p q : α) ↦ p + q
  let l := fun (a b : α) ↦ b - a
  apply sInf_image2_eq_sInf_sInf (u := u) (u₁ := l) (u₂ := l) ?_ ?_
  all_goals simp only [GaloisConnection, tsub_le_iff_right, Function.swap, implies_true, l, u]
  simp_rw [add_comm]
  simp

lemma iInf₂_add {α β ι : Type*} [AddCommMagma ι] [Sub ι] [CompleteLattice ι] [OrderedSub ι]
    {P₁ : α → Prop} {P₂ : β → Prop} {f : α → ι} {g : β → ι} :
    (⨅ (x : α) (_ : P₁ x), f x) + (⨅ (y : β) (_ : P₂ y), g y) =
    ⨅ (x : α) (y : β) (_ : P₁ x) (_ : P₂ y), f x + g y := by
  rw [iInf₂_eq_sInf, iInf₂_eq_sInf, iInf₄_eq_sInf, ← sInf_add']
  congr
  ext y
  rw [Set.mem_add]
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨a, b, ha, hb, rfl⟩
  · rintro ⟨a, b, ha, hb, rfl⟩
    exact ⟨f a, ⟨a, ha, rfl⟩, g b, ⟨b, hb, rfl⟩, rfl⟩

lemma exists_iSup₂_EReal_add {α β : Type*} {P₁ : α → Prop} {P₂ : β → Prop}
    {f : α → EReal} {g : β → EReal} {x : α} (hx : P₁ x) {y : β} (hy : P₂ y)
    (hx_sup : f x = ⨆ (x : α) (_ : P₁ x), f x)
    (hy_sup : g y = ⨆ (y : β) (_ : P₂ y), g y) :
    (⨆ (x : α) (_ : P₁ x), f x) + (⨆ (y : β) (_ : P₂ y), g y) =
    ⨆ (x : α) (y : β) (_ : P₁ x) (_ : P₂ y), f x + g y := by
  refine le_antisymm ?_ ?_
  · rw [← hx_sup, ← hy_sup]
    exact le_iSup₂_of_le x y <| le_iSup₂_of_le hx hy <| le_refl _
  · refine iSup₂_le fun i j ↦ iSup₂_le fun hi hj ↦ ?_
    calc
    _ ≤ (⨆ (x) (_ : P₁ x), f x) + g j := add_le_add_left (le_biSup f hi) _
    _ ≤ (⨆ (x) (_ : P₁ x), f x) + ⨆ (y) (_ : P₂ y), g y := add_le_add_right (le_biSup g hj) _
