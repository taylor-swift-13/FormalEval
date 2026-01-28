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
  problem_73_spec [1%Z; 2%Z; 3%Z; 2%Z; 2%Z; 2%Z; 2%Z; 1%Z; 2%Z; 2%Z] 2%Z.
Proof.
  unfold problem_73_spec, smallest_change_impl.
  simpl.
  (* length arr = 10 *)
  (* half_len = 5 *)
  (* first_half = firstn 5 [1;2;3;2;2;2;2;1;2;2] = [1;2;3;2;2] *)
  (* second_half = skipn (10 - 5) arr = skipn 5 arr = [2;2;1;2;2] *)
  (* rev second_half = [2;2;1;2;2] reversed = [2;2;1;2;2] *)
  (* count_diff [1;2;3;2;2] [2;2;1;2;2] 0 *)
  (* 1 vs 2 -> diff, acc=1 *)
  (* 2 vs 2 -> same, acc=1 *)
  (* 3 vs 1 -> diff, acc=2 *)
  (* 2 vs 2 -> same, acc=2 *)
  (* 2 vs 2 -> same, acc=2 *)
  reflexivity.
Qed.