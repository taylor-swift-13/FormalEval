Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Open Scope Z_scope.

(* 定义一个辅助函数来检查一个整数是否最多有两位数。 *)
Definition is_at_most_two_digits (n : Z) : bool :=
  (Z.ltb (-100) n) && (Z.ltb n 100).

(* 1 <= length arr <= 100 且 1 <= k <= length arr *)
Definition problem_122_pre (arr : list Z) (k : nat) : Prop :=
  (1 <= length arr)%nat /\ (length arr <= 100)%nat /\ (1 <= k)%nat /\ (k <= length arr)%nat.

(* 定义程序规约 Spec *)
Definition problem_122_spec (arr : list Z) (k : nat) (result : Z) : Prop :=
  let first_k_elements := firstn k arr in
  let filtered_elements := filter is_at_most_two_digits first_k_elements in
  result = fold_left Z.add filtered_elements 0.

Definition test_arr := [1%Z; -2%Z; -3%Z; 41%Z; 57%Z; 76%Z; 87%Z; 88%Z; 99%Z].
Definition test_k := 3%nat.

Example problem_122_test :
  problem_122_pre test_arr test_k /\ problem_122_spec test_arr test_k (-4%Z).
Proof.
  split.
  - unfold problem_122_pre. simpl. lia.
  - unfold problem_122_spec. simpl.
    vm_compute. reflexivity.
Qed.