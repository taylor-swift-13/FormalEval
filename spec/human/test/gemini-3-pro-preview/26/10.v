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

Example test_case_new : problem_26_spec [1; 1; 1; 1; 1] [].
Proof.
  unfold problem_26_spec.
  repeat split.
  - (* Case 1: Elements in output must be unique in input *)
    intros j v H.
    destruct j; simpl in H; discriminate.
  - (* Case 2: Unique elements in input must be in output *)
    intros i v H_in H_uniq.
    (* Since all elements in input are 1, v must be 1 *)
    assert (v = 1).
    {
      destruct i; simpl in H_in.
      - injection H_in; auto.
      - destruct i; simpl in H_in.
        + injection H_in; auto.
        + destruct i; simpl in H_in.
          * injection H_in; auto.
          * destruct i; simpl in H_in.
            { injection H_in; auto. }
            { destruct i; simpl in H_in.
              - injection H_in; auto.
              - destruct i; simpl in H_in; discriminate. }
    }
    subst v.
    (* We have v=1. We show that 1 is not unique in input. *)
    (* It appears at index 0 and 1. *)
    assert (H0: nth_error [1; 1; 1; 1; 1] 0 = Some 1). { reflexivity. }
    assert (H1: nth_error [1; 1; 1; 1; 1] 1 = Some 1). { reflexivity. }
    
    (* H_uniq implies that any index k with value 1 must equal i *)
    assert (E0: 0%nat = i). { apply H_uniq. exact H0. }
    assert (E1: 1%nat = i). { apply H_uniq. exact H1. }
    
    (* This leads to 0 = 1, a contradiction *)
    rewrite <- E0 in E1.
    discriminate E1.
  - (* Case 3: Order preservation *)
    intros j1 j2 v1 v2 H1 H2 Hlt.
    destruct j1; simpl in H1; discriminate.
Qed.