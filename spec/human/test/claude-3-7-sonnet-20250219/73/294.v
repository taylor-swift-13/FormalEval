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
    [-10%Z; -9%Z; -8%Z; -7%Z; -6%Z; 0%Z; -5%Z; 17%Z; -4%Z; -3%Z; -2%Z; -1%Z; -1%Z;
     1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 6%Z; 7%Z; 8%Z; -7%Z; 9%Z; 10%Z; -3%Z]
    11%Z.
Proof.
  unfold problem_73_spec, smallest_change_impl.
  simpl.
  (* length arr = 25 *)
  (* half_len = 12 *)
  (* first_half = firstn 12 arr *)
  (*   = [-10;-9;-8;-7;-6;0;-5;17;-4;-3;-2;-1] *)
  (* second_half = skipn (25 - 12) arr = skipn 13 arr *)
  (*   = [1;2;3;4;5;6;7;8;-7;9;10;-3] *)
  (* rev second_half = [-3;10;9;-7;8;7;6;5;4;3;2;1] *)
  (* count_diff first_half rev_second_half 0 *)
  (* Compare element by element: *)
  (* -10 vs -3: diff (1) *)
  (* -9 vs 10: diff (2) *)
  (* -8 vs 9: diff (3) *)
  (* -7 vs -7: same (3) *)
  (* -6 vs 8: diff (4) *)
  (* 0 vs 7: diff (5) *)
  (* -5 vs 6: diff (6) *)
  (* 17 vs 5: diff (7) *)
  (* -4 vs 4: diff (8) *)
  (* -3 vs 3: diff (9) *)
  (* -2 vs 2: diff (10) *)
  (* -1 vs 1: diff (11) *)
  reflexivity.
Qed.