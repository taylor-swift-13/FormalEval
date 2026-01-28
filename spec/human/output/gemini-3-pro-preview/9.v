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

Example test_case_empty : problem_9_spec [] [].
Proof.
  unfold problem_9_spec.
  split.
  - (* Prove length condition *)
    simpl. reflexivity.
  - (* Prove element condition *)
    intros i H.
    simpl in H.
    (* H is (i < 0)%nat, which is a contradiction *)
    lia.
Qed.