Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Arith.Arith Coq.Sorting.Permutation Coq.Sorting.Sorted Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Inductive sum_digits_pos_rel : Z -> Z -> Prop :=
| sdpr_zero : sum_digits_pos_rel 0 0
| sdpr_step : forall n s s_tail,
    0 < n ->
    sum_digits_pos_rel (n / 10) s_tail ->
    s = (n mod 10) + s_tail ->
    sum_digits_pos_rel n s.

Inductive sum_digits_rel : Z -> Z -> Prop :=
| sdr_zero : sum_digits_rel 0 0
| sdr_pos : forall n s,
    0 < n ->
    sum_digits_pos_rel n s ->
    sum_digits_rel n s
| sdr_neg : forall n s p,
    n < 0 ->
    p = Z.abs n ->
    sum_digits_pos_rel p s ->
    sum_digits_rel n s.

Inductive le_stable_rel : (Z * nat) -> (Z * nat) -> Prop :=
| lsr_lt : forall z1 z2 idx1 idx2 s1 s2,
    sum_digits_rel z1 s1 -> sum_digits_rel z2 s2 -> s1 < s2 ->
    le_stable_rel (z1, idx1) (z2, idx2)
| lsr_eq : forall z1 z2 idx1 idx2 s,
    sum_digits_rel z1 s -> sum_digits_rel z2 s -> Nat.le idx1 idx2 ->
    le_stable_rel (z1, idx1) (z2, idx2).

Inductive indexed_list_rel : list Z -> list (Z * nat) -> Prop :=
| ilr_nil : indexed_list_rel nil nil
| ilr_cons : forall h t indexed_tail,
    indexed_list_rel t indexed_tail ->
    indexed_list_rel (h :: t) ((h, 0) :: map (fun '(z, i) => (z, S i)) indexed_tail).

Inductive sorted_stable_rel : list (Z * nat) -> list (Z * nat) -> Prop :=
| ssr_nil : sorted_stable_rel nil nil
| ssr_single : forall p, sorted_stable_rel (p :: nil) (p :: nil)
| ssr_cons : forall p ps sorted_tail,
    le_stable_rel (hd (0, 0) sorted_tail) p ->
    sorted_stable_rel ps sorted_tail ->
    sorted_stable_rel (p :: ps) (p :: sorted_tail).

Definition problem_145_pre (l_in : list Z) : Prop := True.

Definition problem_145_spec (l_in : list Z) (l_out : list Z) : Prop :=
  exists indexed sorted_indexed,
    indexed_list_rel l_in indexed /\
    Permutation indexed sorted_indexed /\
    Sorted le_stable_rel sorted_indexed /\
    l_out = map fst sorted_indexed.

(** Auxiliary lemmas for sum_digits_pos_rel for concrete values **)

(* Prove sum_digits_pos_rel for 1 = 1 *)
Lemma sum_digits_pos_rel_1 : sum_digits_pos_rel 1 1.
Proof.
  apply (sdpr_step 1 1 0).
  - lia.
  - apply sdpr_zero.
  - reflexivity.
Qed.

(* Prove sum_digits_pos_rel for 11 = 2 *)
Lemma sum_digits_pos_rel_11 : sum_digits_pos_rel 11 2.
Proof.
  assert (Hdiv: 11 / 10 = 1) by reflexivity.
  assert (Hmod: 11 mod 10 = 1) by reflexivity.
  rewrite Hdiv, Hmod.
  apply (sdpr_step 11 2 1).
  - lia.
  - apply (sdpr_step 1 1 0); lia.
  - reflexivity.
Qed.

(* Prove sum_digits_pos_rel for 12 = 3 *)
Lemma sum_digits_pos_rel_12 : sum_digits_pos_rel 12 3.
Proof.
  assert (Hdiv: 12 / 10 = 1) by reflexivity.
  assert (Hmod: 12 mod 10 = 2) by reflexivity.
  rewrite Hdiv, Hmod.
  apply (sdpr_step 12 3 1).
  - lia.
  - apply (sdpr_step 1 1 0); lia.
  - reflexivity.
Qed.

(** sum_digits_rel for concrete inputs **)

Lemma sum_digits_rel_0 : sum_digits_rel 0 0.
Proof. apply sdr_zero. Qed.

Lemma sum_digits_rel_1 : sum_digits_rel 1 1.
Proof. apply sdr_pos; lia. apply sum_digits_pos_rel_1. Qed.

Lemma sum_digits_rel_11 : sum_digits_rel 11 2.
Proof. apply sdr_pos; lia. apply sum_digits_pos_rel_11. Qed.

Lemma sum_digits_rel_12 : sum_digits_rel 12 3.
Proof. apply sdr_pos; lia. apply sum_digits_pos_rel_12. Qed.

Lemma sum_digits_rel_neg_1 : sum_digits_rel (-1) 1.
Proof.
  rewrite Z.abs_eq; lia.
  apply sdr_neg with (p := 1); auto.
  apply sum_digits_pos_rel_1.
Qed.

Lemma sum_digits_rel_neg_11 : sum_digits_rel (-11) 2.
Proof.
  rewrite Z.abs_eq; lia.
  apply sdr_neg with (p := 11); auto.
  apply sum_digits_pos_rel_11.
Qed.

Lemma sum_digits_rel_neg_12 : sum_digits_rel (-12) 3.
Proof.
  rewrite Z.abs_eq; lia.
  apply sdr_neg with (p := 12); auto.
  apply sum_digits_pos_rel_12.
Qed.

(** The example proof **)
Example problem_145_example:
  problem_145_spec [1; 11; -1; -11; -12] [-1; -11; 1; -12; 11].
Proof.
  unfold problem_145_spec.
  exists [(1,0); (11,1); (-1,2); (-11,3); (-12,4)].
  exists [(-1,2); (-11,3); (1,0); (-12,4); (11,1)].
  repeat split.
  - apply ilr_cons.
    apply ilr_cons.
    apply ilr_cons.
    apply ilr_cons.
    apply ilr_cons.
    apply ilr_nil.
  - (* Permutation *)
    (* Chain permutations by swaps *)
    apply (Permutation_trans
             (perm_swap (1,0) (11,1) ((-1,2) :: (-11,3) :: (-12,4) :: nil))).
    apply (Permutation_trans
             (perm_swap (11,1) (-1,2) ((1,0) :: (-11,3) :: (-12,4) :: nil))).
    apply (Permutation_trans
             (perm_swap (-11,3) (-12,4) ((11,1) :: (-1,2) :: (1,0) :: nil))).
    apply (Permutation_sym (perm_swap (-1,2) (-11,3) ((11,1) :: (-12,4) :: (1,0) :: nil))).
    apply perm_swap.
  - (* Sorted *)
    econstructor.
    + (* le_stable_rel (-1,2) (-11,3) *)
      apply lsr_lt with (s1:=1) (s2:=2).
      * apply sum_digits_rel_neg_1.
      * apply sum_digits_rel_neg_11.
      * lia.
    + econstructor.
      * (* le_stable_rel (-11,3) (1,0) *)
        apply lsr_lt with (s1 := 2) (s2 := 1).
        -- apply sum_digits_rel_neg_11.
        -- apply sum_digits_rel_1.
        -- lia.
      * econstructor.
        -- (* le_stable_rel (1,0) (-12,4) *)
           apply lsr_lt with (s1 := 1) (s2 := 3).
           ++ apply sum_digits_rel_1.
           ++ apply sum_digits_rel_neg_12.
           ++ lia.
        -- econstructor.
           ++ (* le_stable_rel (-12,4) (11,1) *)
              apply lsr_lt with (s1 := 3) (s2 := 2).
              ** apply sum_digits_rel_neg_12.
              ** apply sum_digits_rel_11.
              ** lia.
           ++ econstructor.
              ** apply ssr_single.
              ** apply ssr_nil.
  - reflexivity.
Qed.