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
  problem_73_spec
    [-10%Z; -9%Z; -8%Z; -7%Z; -6%Z; -5%Z; 17%Z; -4%Z; -3%Z; -2%Z; -1%Z; 0%Z; 1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 6%Z; 7%Z; 8%Z; -7%Z; 9%Z; 10%Z; 10%Z; -5%Z; 6%Z]
    13%Z.
Proof.
  unfold problem_73_spec, smallest_change_impl.
  simpl.
  (* length arr = 26 *)
  (* half_len = 13 *)
  (* first_half = firstn 13 arr = 
     [-10; -9; -8; -7; -6; -5; 17; -4; -3; -2; -1; 0; 1] *)
  (* second_half = skipn (26 - 13) arr = skipn 13 arr = 
     [2;3;4;5;6;7;8;-7;9;10;10;-5;6] *)
  (* rev second_half = [6;-5;10;10;9;-7;8;7;6;5;4;3;2] *)
  (* count_diff on pairs: *)
  (* (-10, 6) diff *)
  (* (-9, -5) diff *)
  (* (-8, 10) diff *)
  (* (-7, 10) diff *)
  (* (-6, 9) diff *)
  (* (-5, -7) diff *)
  (* (17, 8) diff *)
  (* (-4, 7) diff *)
  (* (-3, 6) diff *)
  (* (-2, 5) diff *)
  (* (-1, 4) diff *)
  (* (0, 3) diff *)
  (* (1, 2) diff *)
  (* total differences = 13 *)
  reflexivity.
Qed.