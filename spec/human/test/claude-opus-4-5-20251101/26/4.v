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

Example test_problem_26_duplicates : problem_26_spec [1%Z; 1%Z; 2%Z; 2%Z; 3%Z; 3%Z; 4%Z; 4%Z] [].
Proof.
  unfold problem_26_spec.
  repeat split.
  - intros j v Hj.
    simpl in Hj.
    destruct j; discriminate Hj.
  - intros i v Hi Huniq.
    simpl in Hi.
    destruct i as [|i']; [|destruct i' as [|i']; [|destruct i' as [|i']; [|destruct i' as [|i']; [|destruct i' as [|i']; [|destruct i' as [|i']; [|destruct i' as [|i']; [|destruct i' as [|i']]]]]]]].
    + injection Hi as Hv. rewrite <- Hv in Huniq.
      specialize (Huniq 1%nat). simpl in Huniq.
      assert (1%nat = 0%nat) by (apply Huniq; reflexivity).
      discriminate H.
    + injection Hi as Hv. rewrite <- Hv in Huniq.
      specialize (Huniq 0%nat). simpl in Huniq.
      assert (0%nat = 1%nat) by (apply Huniq; reflexivity).
      discriminate H.
    + injection Hi as Hv. rewrite <- Hv in Huniq.
      specialize (Huniq 3%nat). simpl in Huniq.
      assert (3%nat = 2%nat) by (apply Huniq; reflexivity).
      discriminate H.
    + injection Hi as Hv. rewrite <- Hv in Huniq.
      specialize (Huniq 2%nat). simpl in Huniq.
      assert (2%nat = 3%nat) by (apply Huniq; reflexivity).
      discriminate H.
    + injection Hi as Hv. rewrite <- Hv in Huniq.
      specialize (Huniq 5%nat). simpl in Huniq.
      assert (5%nat = 4%nat) by (apply Huniq; reflexivity).
      discriminate H.
    + injection Hi as Hv. rewrite <- Hv in Huniq.
      specialize (Huniq 4%nat). simpl in Huniq.
      assert (4%nat = 5%nat) by (apply Huniq; reflexivity).
      discriminate H.
    + injection Hi as Hv. rewrite <- Hv in Huniq.
      specialize (Huniq 7%nat). simpl in Huniq.
      assert (7%nat = 6%nat) by (apply Huniq; reflexivity).
      discriminate H.
    + injection Hi as Hv. rewrite <- Hv in Huniq.
      specialize (Huniq 6%nat). simpl in Huniq.
      assert (6%nat = 7%nat) by (apply Huniq; reflexivity).
      discriminate H.
    + destruct i'; discriminate Hi.
  - intros j1 j2 v1 v2 Hj1 Hj2 Hlt.
    simpl in Hj1.
    destruct j1; discriminate Hj1.
Qed.