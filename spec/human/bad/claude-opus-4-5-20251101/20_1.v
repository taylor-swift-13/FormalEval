Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Lia.
Require Import Lra.

Import ListNotations.

Local Open Scope R_scope.

(* Pre: no additional constraints for `find_closest_elements` by default *)
Definition problem_20_pre (input : list R) : Prop := (length input >= 2)%nat.

Definition problem_20_spec (input : list R) (output1 output2 : R) : Prop :=
  (* 1. 前提条件：输入列表长度至少为 2 *)
  (length input >= 2)%nat /\  (* 使用 %nat 明确指出这是自然数比较 *)

  (* 2. 成员条件：output1 和 output2 必须是输入列表中的元素 *)
  In output1 input /\
  In output2 input /\

  (* 3. 顺序条件：output1 小于或等于 output2 *)
  output1 <= output2 /\

  (* 4. 最小距离条件：output1 和 output2 的差的绝对值是最小的 *)
  (forall i j : nat,
    (i < length input)%nat ->
    (j < length input)%nat ->
    i <> j ->
    Rabs (output1 - output2) <= Rabs (nth i input 0 - nth j input 0)).

Example problem_20_test1 :
  problem_20_spec [1.0%R; 2.0%R; 3.9%R; 4.0%R; 5.0%R; 2.2%R] 3.9%R 4.0%R.
Proof.
  unfold problem_20_spec.
  repeat split.
  - (* length >= 2 *)
    simpl. lia.
  - (* In 3.9 input *)
    simpl. right. right. left. reflexivity.
  - (* In 4.0 input *)
    simpl. right. right. right. left. reflexivity.
  - (* 3.9 <= 4.0 *)
    lra.
  - (* minimal distance *)
    intros i j Hi Hj Hij.
    simpl in Hi, Hj.
    (* The list is [1.0; 2.0; 3.9; 4.0; 5.0; 2.2] *)
    (* Distance between 3.9 and 4.0 is 0.1 *)
    assert (Hdist: Rabs (3.9 - 4.0) = 0.1).
    { replace (3.9 - 4.0) with (-0.1) by lra.
      rewrite Rabs_Ropp.
      rewrite Rabs_pos_eq; lra. }
    rewrite Hdist.
    (* Case analysis on i and j *)
    destruct i as [|[|[|[|[|[|i']]]]]]; try lia;
    destruct j as [|[|[|[|[|[|j']]]]]]; try lia;
    simpl;
    try (exfalso; lia);
    try (rewrite Rabs_pos_eq; lra);
    try (rewrite Rabs_minus_sym; rewrite Rabs_pos_eq; lra);
    try (replace (_ - _) with (- _) by lra; rewrite Rabs_Ropp; rewrite Rabs_pos_eq; lra).
Qed.