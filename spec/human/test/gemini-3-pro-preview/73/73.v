Require Import List.
Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

(* count_diff l1 l2 acc := Calculate the number of different elements between l1 and l2 *)
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
  (* Use skipn to get the second half of the list *)
  let second_half := skipn (len - half_len) arr in
  count_diff first_half (rev second_half) 0.

Definition problem_73_pre (arr : list Z) : Prop := True.

Definition problem_73_spec (arr: list Z) (n: Z): Prop :=
  n = smallest_change_impl arr.

Example test_smallest_change: problem_73_spec [1; 1; 2; 3; 3; 3; 1; 4; 4; 2] 4.
Proof.
  unfold problem_73_spec.
  unfold smallest_change_impl.
  (* 
     We can simply compute the result because the input is a concrete list.
     vm_compute is efficient for evaluating arithmetic and list manipulations.
  *)
  vm_compute.
  reflexivity.
Qed.