Require Import List.
Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count_diff (l1 l2: list Z) (acc: Z): Z :=
  match l1, l2 with
  | [], _ => acc
  | _, [] => acc
  | h1 :: t1, h2 :: t2 =>
    if Z.eqb h1 h2 then
      count_diff t1 t2 acc
    else
      count_diff t1 t2 (Z.succ acc)
  end.

Definition smallest_change_impl (arr: list Z): Z :=
  let len := length arr in
  let half_len := (len / 2)%nat in
  let first_half := firstn half_len arr in
  let second_half := skipn (len - half_len) arr in
  count_diff first_half (rev second_half) 0.

Definition problem_73_pre (arr : list Z) : Prop := True.

Definition problem_73_spec (arr: list Z) (n: Z): Prop :=
  n = smallest_change_impl arr.

Example test_smallest_change_1 :
  problem_73_spec [2%Z; 13%Z; 3%Z; 4%Z; 5%Z; 41%Z; 3%Z; 40%Z; 4%Z; 5%Z; 4%Z; 4%Z; 3%Z; 4%Z; 5%Z; 4%Z; 3%Z; 2%Z; 1%Z; 4%Z; 4%Z] 10%Z.
Proof.
  unfold problem_73_spec, smallest_change_impl.
  simpl.
  (* length arr = 21 *)
  (* half_len = 10 *)
  (* first_half = firstn 10 arr = [2;13;3;4;5;41;3;40;4;5] *)
  (* second_half = skipn (21-10) arr = skipn 11 arr = [4;3;4;5;4;3;2;1;4;4] *)
  (* rev second_half = [4;4;1;2;3;4;5;4;3;4] *)
  (* count_diff [2;13;3;4;5;41;3;40;4;5] [4;4;1;2;3;4;5;4;3;4] 0 *)
  (* Compare elements: *)
  (* 2 vs 4 -> diff (1) *)
  (* 13 vs 4 -> diff (2) *)
  (* 3 vs 1 -> diff (3) *)
  (* 4 vs 2 -> diff (4) *)
  (* 5 vs 3 -> diff (5) *)
  (* 41 vs 4 -> diff (6) *)
  (* 3 vs 5 -> diff (7) *)
  (* 40 vs 4 -> diff (8) *)
  (* 4 vs 3 -> diff (9) *)
  (* 5 vs 4 -> diff (10) *)
  reflexivity.
Qed.