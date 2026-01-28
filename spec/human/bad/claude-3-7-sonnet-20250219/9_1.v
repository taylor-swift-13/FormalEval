Require Import List ZArith Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_9_pre : Prop := True.

Definition problem_9_spec (input output : list Z) :=
  length output = length input /\
  forall i,
    (i < length output)%nat ->
    (forall j, (j <= i)%nat -> nth j input 0 <= nth i output 0) /\
    (exists j, (j <= i)%nat /\ nth j input 0 = nth i output 0).

Example problem_9_test_empty :
  problem_9_spec [[]] [].
Proof.
  unfold problem_9_spec.
  split.
  - simpl. reflexivity.
  - intros i Hlen.
    (* length output = 0, so i < 0 impossible *)
    lia.
Qed.