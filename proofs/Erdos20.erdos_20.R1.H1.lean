import OMAReductions.R_Erdos20_erdos_20_R1
import Mathlib

/-!
# The color-coding step of Erdős Problem 20
-/

namespace OMA.Erdos20ColorCoding

open Finset
open scoped BigOperators

/-- Count the colorings for which the restriction to the selected set is a bijection. -/
private lemma card_rainbow {α : Type} [DecidableEq α] {n : ℕ} {A U : Finset α}
    (hAU : A ⊆ U) (hAn : A.card = n) :
    ((univ : Finset (U → Fin n)).filter
      (fun c ↦ Function.Bijective (fun a : A ↦ c ⟨a, hAU a.property⟩))).card =
        n.factorial * n ^ (U.card - n) := by
  classical
  let B := {u : U // (u : α) ∈ A}
  let D := {u : U // (u : α) ∉ A}
  let R := {c : U → Fin n // Function.Bijective (fun a : A ↦ c ⟨a, hAU a.property⟩)}
  let e : R ≃ (A ≃ Fin n) × (D → Fin n) :=
    { toFun := fun c ↦ ⟨Equiv.ofBijective _ c.property, fun u ↦ c.val u⟩
      invFun := fun p ↦
        ⟨fun u ↦ if h : (u : α) ∈ A then p.1 ⟨u, h⟩ else p.2 ⟨u, h⟩, by
          convert p.1.bijective using 1
          funext a
          simp only [a.property, dite_true]⟩
      left_inv := by
        intro c
        apply Subtype.ext
        funext u
        by_cases h : (u : α) ∈ A <;> simp [h]
      right_inv := by
        intro p
        apply Prod.ext
        · apply Equiv.ext
          intro a
          simp only [Equiv.ofBijective_apply, a.property, dite_true]
        · funext u
          simp only [u.property, dite_false]
          rfl }
  have hB : Fintype.card B = n := by
    let eB : B ≃ A :=
      { toFun := fun b ↦ ⟨b.val, b.property⟩
        invFun := fun a ↦ ⟨⟨a, hAU a.property⟩, a.property⟩
        left_inv := fun b ↦ Subtype.ext (Subtype.ext rfl)
        right_inv := fun a ↦ Subtype.ext rfl }
    rw [Fintype.card_congr eB, Fintype.card_coe, hAn]
  have hD : Fintype.card D = U.card - n := by
    unfold D
    rw [Fintype.card_subtype_compl, Fintype.card_coe, ← hB]
  have hE : Fintype.card (A ≃ Fin n) = n.factorial := by
    have eA : A ≃ Fin n := Fintype.equivFinOfCardEq (by simpa using hAn)
    rw [Fintype.card_equiv eA, Fintype.card_coe, hAn]
  rw [← Fintype.card_subtype, show Fintype.card R = _ from Fintype.card_congr e,
    Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, hD, hE]

end OMA.Erdos20ColorCoding

open Finset
open scoped BigOperators

theorem OMA.solution : OMA.R_Erdos20_erdos_20_R1.H1 := by
  classical
  intro α n hn F hF
  let z : Fin n := ⟨0, hn⟩
  by_cases hFe : F.Nonempty
  · let U : Finset α := F.biUnion id
    have hAU (A : Finset α) (hA : A ∈ F) : A ⊆ U := by
      intro a ha
      exact mem_biUnion.mpr ⟨A, hA, ha⟩
    let extend (c : U → Fin n) (a : α) : Fin n :=
      if ha : a ∈ U then c ⟨a, ha⟩ else z
    let G (c : U → Fin n) : Finset (Finset α) :=
      F.filter fun (A : Finset α) ↦ Function.Bijective (fun a : A ↦ extend c a)
    have hG A (hA : A ∈ F) :
        ((univ : Finset (U → Fin n)).filter
          (fun c ↦ Function.Bijective (fun a : A ↦ extend c a))).card =
            n.factorial * n ^ (U.card - n) := by
      convert OMA.Erdos20ColorCoding.card_rainbow (hAU A hA) (hF A hA) using 2
      ext c
      simp only [mem_filter, mem_univ, true_and]
      have he : (fun a : A ↦ extend c a) = (fun a : A ↦ c ⟨a, hAU A hA a.property⟩) :=
        funext fun a ↦ dif_pos (hAU A hA a.property)
      rw [he]
    have hsum : ∑ c : U → Fin n, (G c).card = F.card * (n.factorial * n ^ (U.card - n)) := by
      simp_rw [G, card_filter]
      rw [sum_comm]
      simp_rw [← card_filter]
      rw [sum_congr rfl hG, sum_const, nsmul_eq_mul]
      simp
    have : Nonempty (U → Fin n) := ⟨fun _ ↦ z⟩
    obtain ⟨c, -, hmax⟩ := exists_max_image (univ : Finset (U → Fin n)) (fun c ↦ (G c).card)
      univ_nonempty
    refine ⟨extend c, G c, filter_subset _ _, (fun A hA ↦ (mem_filter.mp hA).2), ?_⟩
    have hsum_le : ∑ c' : U → Fin n, (G c').card ≤ n ^ U.card * (G c).card := by
      calc
        ∑ c' : U → Fin n, (G c').card ≤ ∑ _c' : U → Fin n, (G c).card :=
          sum_le_sum hmax
        _ = n ^ U.card * (G c).card := by
          rw [sum_const, nsmul_eq_mul, card_univ, Fintype.card_fun, Fintype.card_fin,
            Fintype.card_coe]
          simp
    obtain ⟨A, hA⟩ := hFe
    have hnu : n ≤ U.card := hF A hA ▸ card_le_card (hAU A hA)
    have hpow : n ^ U.card = n ^ n * n ^ (U.card - n) := by
      rw [← pow_add, Nat.add_sub_of_le hnu]
    rw [hsum, hpow] at hsum_le
    apply Nat.le_of_mul_le_mul_right _ (pow_pos hn (U.card - n))
    simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hsum_le
  · have hF0 := not_nonempty_iff_eq_empty.mp hFe
    subst F
    exact ⟨fun _ ↦ z, ∅, by simp, by simp, by simp⟩


