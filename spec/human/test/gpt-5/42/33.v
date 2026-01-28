Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.

Definition problem_42_pre (input : list Z) : Prop := True.

Definition problem_42_spec(input output : list Z) : Prop :=
  length input = length output /\
  forall i : nat, i < length output -> nth i output 0%Z = ((nth i input 0%Z) + 1)%Z.

Example problem_42_test_nonempty : problem_42_spec [1%Z; 1%Z; 1%Z; 1%Z; 10%Z; 1%Z; 1%Z] [2%Z; 2%Z; 2%Z; 2%Z; 11%Z; 2%Z; 2%Z].
Proof.
  unfold problem_42_spec.
  simpl.
  split.
  - reflexivity.
  - intros i Hi.
    destruct i as [|i1].
    + simpl. lia.
    + destruct i1 as [|i2].
      * simpl. lia.
      * destruct i2 as [|i3].
        { simpl. lia. }
        { destruct i3 as [|i4].
          - simpl. lia.
          - destruct i4 as [|i5].
            + simpl. lia.
            + destruct i5 as [|i6].
              * simpl. lia.
              * destruct i6 as [|i7].
                { simpl. lia. }
                { exfalso. lia. } }
Qed.