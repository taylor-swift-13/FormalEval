Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Arith.Arith Permutation Sorting.Sorted.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Inductive sum_digits_pos_rel : Z -> Z -> Prop :=
| sdpr_zero : sum_digits_pos_rel 0%Z 0%Z
| sdpr_step : forall n s s_tail, 0 < n -> sum_digits_pos_rel (n / 10) s_tail ->
   s = (n mod 10) + s_tail -> sum_digits_pos_rel n s.

Inductive sum_digits_rel : Z -> Z -> Prop :=
| sdr_zero : sum_digits_rel 0%Z 0%Z
| sdr_pos : forall n s, 0 < n -> sum_digits_pos_rel n s -> sum_digits_rel n s
| sdr_neg : forall n s p, n < 0 -> p = Z.abs n -> sum_digits_pos_rel p s ->
   sum_digits_rel n s.

Inductive le_stable_rel : (Z * nat) -> (Z * nat) -> Prop :=
| lsr_lt : forall z1 z2 (idx1 idx2 : nat) s1 s2,
   sum_digits_rel z1 s1 -> sum_digits_rel z2 s2 -> s1 < s2 ->
   le_stable_rel (z1, idx1) (z2, idx2)
| lsr_eq : forall z1 z2 (idx1 idx2 : nat) s,
   sum_digits_rel z1 s -> sum_digits_rel z2 s -> Nat.le idx1 idx2 ->
   le_stable_rel (z1, idx1) (z2, idx2).

Inductive indexed_list_rel : list Z -> list (Z * nat) -> Prop :=
| ilr_nil : indexed_list_rel nil nil
| ilr_cons : forall h t indexed_tail, indexed_list_rel t indexed_tail ->
    indexed_list_rel (h :: t) ((h, 0%nat) :: map (fun '(z, i) => (z, S i)) indexed_tail).

Inductive sorted_stable_rel : list (Z * nat) -> list (Z * nat) -> Prop :=
| ssr_nil : sorted_stable_rel nil nil
| ssr_single : forall p, sorted_stable_rel (p :: nil) (p :: nil)
| ssr_cons : forall p ps sorted_tail, le_stable_rel (hd (0%Z, 0%nat) sorted_tail) p ->
    sorted_stable_rel ps sorted_tail ->
    sorted_stable_rel (p :: ps) (p :: sorted_tail).

Definition problem_145_pre (l_in : list Z) : Prop := True.

Definition problem_145_spec (l_in : list Z) (l_out : list Z) : Prop :=
  exists indexed sorted_indexed, indexed_list_rel l_in indexed /\
    Permutation indexed sorted_indexed /\
    Sorted le_stable_rel sorted_indexed /\
    l_out = map fst sorted_indexed.

(* Helper lemmas *)
Lemma sdpr_1 : sum_digits_pos_rel 1 1.
Proof.
  refine (sdpr_step 1 1 0 _ _ _).
  - lia.
  - apply sdpr_zero.
  - reflexivity.
Qed.

Lemma sdpr_11 : sum_digits_pos_rel 11 2.
Proof.
  refine (sdpr_step 11 2 1 _ _ _).
  - lia.
  - refine (sdpr_step 1 1 0 _ _ _).
    + lia.
    + apply sdpr_zero.
    + reflexivity.
  - reflexivity.
Qed.

Lemma sdpr_12 : sum_digits_pos_rel 12 3.
Proof.
  refine (sdpr_step 12 3 1 _ _ _).
  - lia.
  - refine (sdpr_step 1 1 0 _ _ _).
    + lia.
    + apply sdpr_zero.
    + reflexivity.
  - reflexivity.
Qed.

Lemma sdr_1 : sum_digits_rel 1 1.
Proof.
  apply sdr_pos with (s := 1).
  - lia.
  - apply sdpr_1.
Qed.

Lemma sdr_neg1 : sum_digits_rel (-1) 1.
Proof.
  apply sdr_neg with (p := 1).
  - lia.
  - reflexivity.
  - apply sdpr_1.
Qed.

Lemma sdr_11 : sum_digits_rel 11 2.
Proof.
  apply sdr_pos with (s := 2).
  - lia.
  - apply sdpr_11.
Qed.

Lemma sdr_neg11 : sum_digits_rel (-11) 2.
Proof.
  apply sdr_neg with (p := 11).
  - lia.
  - reflexivity.
  - apply sdpr_11.
Qed.

Lemma sdr_neg12 : sum_digits_rel (-12) 3.
Proof.
  apply sdr_neg with (p := 12).
  - lia.
  - reflexivity.
  - apply sdpr_12.
Qed.

Example problem_145_example : problem_145_spec [1; 11; -1; -11; -12] [-1; -11; 1; -12; 11].
Proof.
  unfold problem_145_spec.
  exists [(-1, 0%nat); (-11, 1%nat); (1, 2%nat); (-12, 3%nat); (11, 4%nat)].
  exists [(-1, 0%nat); (-11, 1%nat); (1, 2%nat); (-12, 3%nat); (11, 4%nat)].
  split.
  - refine (ilr_cons 1 [11; -1; -11; -12] [(-11, 0%nat); (1, 1%nat); (-12, 2%nat); (11, 3%nat)] _).
    refine (ilr_cons 11 [-1; -11; -12] [(-1, 0%nat); (-12, 1%nat); (11, 2%nat)] _).
    refine (ilr_cons (-1) [-11; -12] [(-12, 0%nat); (11, 1%nat)] _).
    refine (ilr_cons (-11) [-12] [(11, 0%nat)] _).
    refine (ilr_cons (-12) [] [] _).
    apply ilr_nil.
  - split.
    + apply Permutation_refl.
    + split.
      * constructor.
        { constructor 2 with (s1 := 1) (s2 := 2).
          - apply sdr_neg1.
          - apply sdr_neg11.
          - lia.
        }
        constructor.
        { constructor 2 with (s1 := 2) (s2 := 1).
          - apply sdr_neg11.
          - apply sdr_1.
          - lia.
        }
        constructor.
        { constructor 2 with (s1 := 1) (s2 := 3).
          - apply sdr_1.
          - apply sdr_neg12.
          - lia.
        }
        constructor.
        { constructor 2 with (s1 := 3) (s2 := 2).
          - apply sdr_neg12.
          - apply sdr_11.
          - lia.
        }
        constructor.
      * reflexivity.
Qed.