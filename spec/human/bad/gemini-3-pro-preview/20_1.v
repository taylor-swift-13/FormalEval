Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lra.
Require Import Coq.micromega.Lia.

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

(* Test case definition *)
Definition input_ex : list R := [1.0; 2.0; 3.9; 4.0; 5.0; 2.2].
Definition out1_ex : R := 3.9.
Definition out2_ex : R := 4.0.

Example problem_20_test_case : problem_20_spec input_ex out1_ex out2_ex.
Proof.
  unfold problem_20_spec, input_ex, out1_ex, out2_ex.
  repeat split.
  (* 1. Length condition *)
  - simpl. lia.
  (* 2. Membership output1 *)
  - simpl. tauto.
  (* 3. Membership output2 *)
  - simpl. tauto.
  (* 4. Order condition *)
  - lra.
  (* 5. Minimal distance condition *)
  - intros i j Hi Hj Hneq.
    (* We manually destruct i and j to cover all indices 0..5. 
       The 'destruct i as [|i]' pattern ensures the variable name 'i' is preserved 
       for the successor case. The nested structure correctly generates 6 goals. *)
    destruct i as [|i]; [| destruct i as [|i]; [| destruct i as [|i]; [| destruct i as [|i]; [| destruct i as [|i]; [| destruct i as [|i]; [| simpl in Hi; lia ]]]]]].
    (* For each of the 6 goals (values of i), we destruct j similarly. 
       Using 'all:' applies the tactic to all generated subgoals. *)
    all: destruct j as [|j]; [| destruct j as [|j]; [| destruct j as [|j]; [| destruct j as [|j]; [| destruct j as [|j]; [| destruct j as [|j]; [| simpl in Hj; lia ]]]]]].
    (* Eliminate cases where i = j *)
    all: try (exfalso; lia).
    (* Simplify nth access and solve real inequalities for all remaining pairs *)
    all: simpl; lra.
Qed.