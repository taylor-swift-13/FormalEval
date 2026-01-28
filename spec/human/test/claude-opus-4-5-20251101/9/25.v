Require Import List ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_9_pre : Prop := True.

Definition problem_9_spec (input output : list Z) :=
  length output = length input /\
  forall i,
    (i < length output)%nat ->
    (forall j, (j <= i)%nat -> nth j input 0 <= nth i output 0) /\
    (exists j, (j <= i)%nat /\ nth j input 0 = nth i output 0).

Example test_problem_9 : problem_9_spec [4%Z; 4%Z; -3%Z; -4%Z; -5%Z; -4%Z; -3%Z; -2%Z; -1%Z; -2%Z] [4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z].
Proof.
  unfold problem_9_spec.
  split.
  - reflexivity.
  - intros i H.
    split.
    + intros j Hj.
      do 10 (destruct i; [do 10 (destruct j; [simpl; lia | ]); simpl in Hj; lia | ]).
      simpl in H. lia.
    + do 10 (destruct i; [exists 0%nat; split; [lia | reflexivity] | ]).
      simpl in H. lia.
Qed.