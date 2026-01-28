Require Import List.
Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Inductive count_diff_rel : list Z -> list Z -> Z -> Z -> Prop :=
  | cdr_nil1 : forall l2 acc, count_diff_rel [] l2 acc acc
  | cdr_nil2 : forall l1 acc, count_diff_rel l1 [] acc acc
  | cdr_eq : forall h1 h2 t1 t2 acc result,
      Z.eqb h1 h2 = true ->
      count_diff_rel t1 t2 acc result ->
      count_diff_rel (h1 :: t1) (h2 :: t2) acc result
  | cdr_neq : forall h1 h2 t1 t2 acc result,
      Z.eqb h1 h2 = false ->
      count_diff_rel t1 t2 (Z.succ acc) result ->
      count_diff_rel (h1 :: t1) (h2 :: t2) acc result.

Definition problem_73_pre (arr : list Z) : Prop := True.

Definition problem_73_spec (arr: list Z) (n: Z): Prop :=
  exists len half_len first_half second_half,
    len = length arr /\
    half_len = (len / 2)%nat /\
    first_half = firstn half_len arr /\
    second_half = skipn (len - half_len) arr /\
    count_diff_rel first_half (rev second_half) 0 n.

Example problem_73_test_case :
  problem_73_spec [1%Z; 2%Z; 3%Z; 5%Z; 4%Z; 7%Z; 9%Z; 6%Z] 4%Z.
Proof.
  unfold problem_73_spec.
  exists 8%nat.
  exists 4%nat.
  exists [1%Z; 2%Z; 3%Z; 5%Z].
  exists [4%Z; 7%Z; 9%Z; 6%Z].
  repeat split.
  - simpl. reflexivity.
  - compute. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl.
    apply cdr_neq.
    + simpl. reflexivity.
    + simpl.
      apply cdr_neq.
      * simpl. reflexivity.
      * simpl.
        apply cdr_neq.
        -- simpl. reflexivity.
        -- simpl.
           apply cdr_neq.
           ++ simpl. reflexivity.
           ++ simpl.
              apply cdr_nil1.
Qed.