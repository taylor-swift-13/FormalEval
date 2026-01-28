Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
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
  let second_half := skipn (len - half_len)%nat arr in
  count_diff first_half (rev second_half) 0.

Definition problem_73_pre (arr : list Z) : Prop := True.

Definition problem_73_spec (arr: list Z) (n: Z): Prop :=
  n = smallest_change_impl arr.

Example problem_73_test_case_1 :
  problem_73_spec [1%Z; 2%Z; 4%Z; 6%Z; 0%Z; 6%Z; 7%Z; 8%Z; 10%Z; 10%Z; 9%Z; 8%Z; 7%Z; 6%Z; 4%Z; 3%Z; 2%Z; 1%Z] 6%Z.
Proof.
  unfold problem_73_spec, smallest_change_impl.
  vm_compute.
  reflexivity.
Qed.