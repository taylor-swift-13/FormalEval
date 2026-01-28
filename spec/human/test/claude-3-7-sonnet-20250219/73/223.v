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
  problem_73_spec [1%Z; 1%Z; 1%Z; 1%Z; 2%Z; 2%Z; 2%Z; 12%Z; 2%Z; 28%Z; 1%Z; 2%Z; 1%Z; 3%Z; 1%Z; 1%Z; 1%Z; 2%Z; 2%Z; 2%Z; 1%Z] 9%Z.
Proof.
  unfold problem_73_spec, smallest_change_impl.
  simpl.
  (* length arr = 21 *)
  (* half_len = 10 *)
  (* first_half = firstn 10 arr = [1;1;1;1;2;2;2;12;2;28] *)
  (* second_half = skipn (21 - 10) arr = skipn 11 arr = [2;1;3;1;1;1;2;2;2;1] *)
  (* rev second_half = [1;2;2;2;1;1;1;3;1;2] *)
  (* count_diff first_half rev_second_half 0 *)
  (* Compare: *)
  (* 1 vs 1 equal acc=0 *)
  (* 1 vs 2 diff acc=1 *)
  (* 1 vs 2 diff acc=2 *)
  (* 1 vs 2 diff acc=3 *)
  (* 2 vs 1 diff acc=4 *)
  (* 2 vs 1 diff acc=5 *)
  (* 2 vs 1 diff acc=6 *)
  (* 12 vs 3 diff acc=7 *)
  (* 2 vs 1 diff acc=8 *)
  (* 28 vs 2 diff acc=9 *)
  reflexivity.
Qed.