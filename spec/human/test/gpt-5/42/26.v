Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.

Definition problem_42_pre (input : list Z) : Prop := True.

Definition problem_42_spec(input output : list Z) : Prop :=
  length input = length output /\
  forall i : nat, i < length output -> nth i output 0%Z = ((nth i input 0%Z) + 1)%Z.

Example problem_42_test_zeros : problem_42_spec [0%Z; 0%Z; 0%Z; 0%Z; 0%Z] [1%Z; 1%Z; 1%Z; 1%Z; 1%Z].
Proof.
  unfold problem_42_spec.
  simpl.
  split.
  - reflexivity.
  - intros i Hi.
    destruct i as [|i1].
    + simpl. reflexivity.
    + assert (i1 < 4)%nat by lia.
      destruct i1 as [|i2].
      * simpl. reflexivity.
      * assert (i2 < 3)%nat by lia.
        destruct i2 as [|i3].
        { simpl. reflexivity. }
        assert (i3 < 2)%nat by lia.
        destruct i3 as [|i4].
        { simpl. reflexivity. }
        assert (i4 < 1)%nat by lia.
        destruct i4 as [|i5].
        { simpl. reflexivity. }
        exfalso. lia.
Qed.