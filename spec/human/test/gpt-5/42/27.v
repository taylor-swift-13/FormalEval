Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.

Definition problem_42_pre (input : list Z) : Prop := True.

Definition problem_42_spec(input output : list Z) : Prop :=
  length input = length output /\
  forall i : nat, i < length output -> nth i output 0%Z = ((nth i input 0%Z) + 1)%Z.

Example problem_42_test_case : problem_42_spec [2%Z; 2%Z; 500%Z; 3%Z] [3%Z; 3%Z; 501%Z; 4%Z].
Proof.
  unfold problem_42_spec.
  simpl.
  split.
  - reflexivity.
  - intros i Hi.
    destruct i as [|i1].
    + simpl. reflexivity.
    + simpl.
      destruct i1 as [|i2].
      * simpl. reflexivity.
      * simpl.
        destruct i2 as [|i3].
        { simpl. reflexivity. }
        { destruct i3 as [|i4].
          - simpl. reflexivity.
          - exfalso. lia. }
Qed.