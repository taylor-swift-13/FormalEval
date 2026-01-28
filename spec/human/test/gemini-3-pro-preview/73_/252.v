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

Example test_case : problem_73_spec [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 6%Z; 14%Z; 7%Z; 8%Z; 9%Z; 10%Z; 11%Z; 12%Z; 13%Z; 14%Z; 15%Z; 16%Z; 10%Z; 17%Z; 18%Z; 19%Z; 20%Z; 21%Z; 22%Z; 23%Z; 24%Z; 25%Z; 26%Z; 27%Z; 28%Z; 29%Z; 30%Z; 31%Z; 32%Z; 33%Z; 34%Z; 35%Z; 36%Z; 38%Z; 39%Z; 40%Z; 41%Z; 42%Z; 43%Z; 44%Z; 45%Z; 46%Z; 47%Z; 48%Z; 49%Z; 50%Z; 2%Z; 27%Z] 25%Z.
Proof.
  unfold problem_73_spec.
  exists 53%nat.
  exists 26%nat.
  exists [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 6%Z; 14%Z; 7%Z; 8%Z; 9%Z; 10%Z; 11%Z; 12%Z; 13%Z; 14%Z; 15%Z; 16%Z; 10%Z; 17%Z; 18%Z; 19%Z; 20%Z; 21%Z; 22%Z; 23%Z; 24%Z].
  exists [26%Z; 27%Z; 28%Z; 29%Z; 30%Z; 31%Z; 32%Z; 33%Z; 34%Z; 35%Z; 36%Z; 38%Z; 39%Z; 40%Z; 41%Z; 42%Z; 43%Z; 44%Z; 45%Z; 46%Z; 47%Z; 48%Z; 49%Z; 50%Z; 2%Z; 27%Z].
  split. { reflexivity. }
  split. { reflexivity. }
  split. { reflexivity. }
  split. { reflexivity. }
  simpl.
  apply cdr_neq. { reflexivity. }
  apply cdr_eq. { reflexivity. }
  apply cdr_neq. { reflexivity. }
  apply cdr_neq. { reflexivity. }
  apply cdr_neq. { reflexivity. }
  apply cdr_neq. { reflexivity. }
  apply cdr_neq. { reflexivity. }
  apply cdr_neq. { reflexivity. }
  apply cdr_neq. { reflexivity. }
  apply cdr_neq. { reflexivity. }
  apply cdr_neq. { reflexivity. }
  apply cdr_neq. { reflexivity. }
  apply cdr_neq. { reflexivity. }
  apply cdr_neq. { reflexivity. }
  apply cdr_neq. { reflexivity. }
  apply cdr_neq. { reflexivity. }
  apply cdr_neq. { reflexivity. }
  apply cdr_neq. { reflexivity. }
  apply cdr_neq. { reflexivity. }
  apply cdr_neq. { reflexivity. }
  apply cdr_neq. { reflexivity. }
  apply cdr_neq. { reflexivity. }
  apply cdr_neq. { reflexivity. }
  apply cdr_neq. { reflexivity. }
  apply cdr_neq. { reflexivity. }
  apply cdr_neq. { reflexivity. }
  apply cdr_nil1.
Qed.