Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.

Definition problem_42_pre (input : list Z) : Prop := True.

Definition problem_42_spec(input output : list Z) : Prop :=
  length input = length output /\
  forall i : nat, i < length output -> nth i output 0%Z = ((nth i input 0%Z) + 1)%Z.

Example problem_42_test_case : problem_42_spec [10%Z; 100%Z; 1000%Z; 10%Z] [11%Z; 101%Z; 1001%Z; 11%Z].
Proof.
  unfold problem_42_spec.
  simpl.
  split.
  - reflexivity.
  - intros i Hi.
    destruct i as [|i].
    + simpl. reflexivity.
    + destruct i as [|i].
      * simpl. reflexivity.
      * destruct i as [|i].
        { simpl. reflexivity. }
        { destruct i as [|i].
          - simpl. reflexivity.
          - exfalso. lia. }
Qed.