(* 引入必要的库 *)
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Init.Nat.
Import ListNotations.
Local Open Scope Z_scope.

Definition problem_26_pre (input : list Z): Prop := True.

(* 程序规约 Spec 的 Coq 定义 *)
Definition problem_26_spec (input : list Z) (output : list Z) : Prop :=
  (*  1: output 中的每个元素 v 都存在于 input 中，
     并且 v 在 input 中是唯一的。 *)
  (forall (j : nat) (v : Z),
     nth_error output j = Some v ->
     (exists i : nat,
        nth_error input i = Some v /\
        (forall k : nat, nth_error input k = Some v -> k = i))) /\

  (*  2: input 中任何只出现一次的元素，也必须出现在 output 中。 *)
  (forall (i : nat) (v : Z),
     nth_error input i = Some v ->
     (forall k : nat, nth_error input k = Some v -> k = i) ->
     In v output) /\

  (*  3: output 中元素的相对顺序与它们在 input 中的相对顺序保持一致。 *)
  (forall (j1 j2 : nat) (v1 v2 : Z),
     nth_error output j1 = Some v1 ->
     nth_error output j2 = Some v2 ->
     (j1 < j2)%nat ->
     (exists i1 i2 : nat,
        nth_error input i1 = Some v1 /\
        nth_error input i2 = Some v2 /\
        (i1 < i2)%nat)).

Example test_problem_26_empty : problem_26_spec [] [].
Proof.
  unfold problem_26_spec.
  repeat split.
  - (* Condition 1: output 中的每个元素都在 input 中且唯一 *)
    intros j v Hj.
    simpl in Hj.
    destruct j; discriminate Hj.
  - (* Condition 2: input 中唯一的元素出现在 output 中 *)
    intros i v Hi Huniq.
    simpl in Hi.
    destruct i; discriminate Hi.
  - (* Condition 3: 保持相对顺序 *)
    intros j1 j2 v1 v2 Hj1 Hj2 Hlt.
    simpl in Hj1.
    destruct j1; discriminate Hj1.
Qed.