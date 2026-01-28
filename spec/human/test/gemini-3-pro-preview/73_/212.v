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

Example test_case : problem_73_spec [1; 2; 3; 4; 5; 6; 14; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 27; 30; 31; 32; 33; 34; 35; 36; 37; 44; 38; 39; 40; 41; 42; 43; 44; 45; 46; 47; 48; 49; 50; 2] 27.
Proof.
  unfold problem_73_spec.
  exists 54%nat.
  exists 27%nat.
  exists [1; 2; 3; 4; 5; 6; 14; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26]%Z.
  exists [27; 28; 29; 27; 30; 31; 32; 33; 34; 35; 36; 37; 44; 38; 39; 40; 41; 42; 43; 44; 45; 46; 47; 48; 49; 50; 2]%Z.
  split. { reflexivity. } (* len = length arr *)
  split. { reflexivity. } (* half_len = len / 2 *)
  split. { reflexivity. } (* first_half = firstn half_len arr *)
  split. { reflexivity. } (* second_half = skipn (len - half_len) arr *)
  
  (* Now proving count_diff_rel *)
  simpl.
  repeat (apply cdr_neq; [ reflexivity | ]).
  apply cdr_nil1.
Qed.