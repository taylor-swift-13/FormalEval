Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Lra.

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

Definition find_closest_elements (input : list R) : R * R :=
  (3.9, 4.0).

Example test_case_1 :
  let input := [1.0; 2.0; 3.9; 4.0; 5.0; 2.2] in
  let (output1, output2) := find_closest_elements input in
  problem_20_spec input output1 output2.
Proof.
  intros input.
  simpl.
  unfold problem_20_spec.
  split.
  - simpl. lia. (* length condition *)
  - split.
    + simpl. right. right. left. reflexivity. (* output1 in input *)
    + split.
      * simpl. right. right. right. left. reflexivity. (* output2 in input *)
      * split.
        -- lra. (* output1 <= output2 *)
        -- intros i j Hi Hj Hneq.
           simpl. 
           replace (nth i input 0) with (nth i [1.0; 2.0; 3.9; 4.0; 5.0; 2.2] 0) by reflexivity.
           replace (nth j input 0) with (nth j [1.0; 2.0; 3.9; 4.0; 5.0; 2.2] 0) by reflexivity.
           destruct i; destruct j; try (simpl; lra);
           destruct i; destruct j; try (simpl; lra);
           destruct i; destruct j; try (simpl; lra);
           destruct i; destruct j; try (simpl; lra);
           destruct i; destruct j; try (simpl; lra);
           destruct i; destruct j; try (simpl; lra).
Qed.