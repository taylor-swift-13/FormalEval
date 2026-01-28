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

Example test_case : problem_73_spec [1; 2; 3; 4; 5; 3; 1; 1; 2; 4; 4; 5; 5; 3] 5.
Proof.
  unfold problem_73_spec.
  exists 14%nat.
  exists 7%nat.
  exists [1; 2; 3; 4; 5; 3; 1]%Z.
  exists [1; 2; 4; 4; 5; 5; 3]%Z.
  split. { reflexivity. } (* len = length arr *)
  split. { reflexivity. } (* half_len = len / 2 *)
  split. { reflexivity. } (* first_half = firstn half_len arr *)
  split. { reflexivity. } (* second_half = skipn (len - half_len) arr *)
  
  (* Now proving count_diff_rel *)
  simpl.
  (* 1 vs 3: neq *)
  apply cdr_neq. { reflexivity. }
  (* 2 vs 5: neq *)
  apply cdr_neq. { reflexivity. }
  (* 3 vs 5: neq *)
  apply cdr_neq. { reflexivity. }
  (* 4 vs 4: eq *)
  apply cdr_eq. { reflexivity. }
  (* 5 vs 4: neq *)
  apply cdr_neq. { reflexivity. }
  (* 3 vs 2: neq *)
  apply cdr_neq. { reflexivity. }
  (* 1 vs 1: eq *)
  apply cdr_eq. { reflexivity. }
  (* Base case *)
  apply cdr_nil1.
Qed.