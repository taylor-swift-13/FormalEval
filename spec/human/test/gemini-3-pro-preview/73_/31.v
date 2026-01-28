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

Example test_case : problem_73_spec [1; 2; 3; 2; 2; 2; 2; 2; 1; 2] 3.
Proof.
  unfold problem_73_spec.
  exists 10%nat.
  exists 5%nat.
  exists [1; 2; 3; 2; 2]%Z.
  exists [2; 2; 2; 1; 2]%Z.
  split. { reflexivity. }
  split. { reflexivity. }
  split. { reflexivity. }
  split. { reflexivity. }
  
  simpl.
  apply cdr_neq. { reflexivity. }
  apply cdr_neq. { reflexivity. }
  apply cdr_neq. { reflexivity. }
  apply cdr_eq. { reflexivity. }
  apply cdr_eq. { reflexivity. }
  apply cdr_nil1.
Qed.