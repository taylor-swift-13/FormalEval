Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition problem_34_pre (input : list Z) : Prop := True.

Definition problem_34_spec (input : list Z) (output : list Z) : Prop :=
  Sorted Z.le output /\
  NoDup output /\
  (forall z, In z input <-> In z output).

Example problem_34_test :
  problem_34_spec [5; 3; 5; 2; 3; 3; 9; 0; 123] [0; 2; 3; 5; 9; 123].
Proof.
  unfold problem_34_spec.
  split; [| split].
  - (* Sorted Z.le [0; 2; 3; 5; 9; 123] *)
    repeat constructor; lia.
  - (* NoDup [0; 2; 3; 5; 9; 123] *)
    constructor.
    { simpl. intros [H|[H|[H|[H|[H|H]]]]]; discriminate. }
    constructor.
    { simpl. intros [H|[H|[H|[H|H]]]]; discriminate. }
    constructor.
    { simpl. intros [H|[H|[H|H]]]; discriminate. }
    constructor.
    { simpl. intros [H|[H|[H|H]]]; discriminate. }
    constructor.
    { simpl. intros [H|[H|H]]; discriminate. }
    constructor.
    { simpl. intros H; exact H. }
    constructor.
  - (* forall z, In z input <-> In z output *)
    intros z; split; simpl; intros H.
    + destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]; subst; auto.
    + destruct H as [H|[H|[H|[H|[H|[H|H]]]]]]; subst; auto.
Qed.