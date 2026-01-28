Require Import List ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition problem_9_spec (input output : list Z) :=
  length output = length input /\
  forall i,
    (i < length output)%nat ->
    (forall j, (j <= i)%nat -> nth j input 0 <= nth i output 0) /\
    (exists j, (j <= i)%nat /\ nth j input 0 = nth i output 0).

Example test_example2 : problem_9_spec [[50%Z; 40%Z; 30%Z; 20%Z; 10%Z]] [50%Z; 50%Z; 50%Z; 50%Z; 50%Z].
Proof.
  unfold problem_9_spec.
  split.
  - simpl.
    reflexivity.
  - intros i H.
    simpl in H.
    destruct i as [|i'].
    + exists 0; split.
      * lia.
      * simpl. reflexivity.
    + destruct i' as [|i''].
      * exists 0; split.
        -- lia.
        -- simpl. reflexivity.
      * exists 0; split.
        -- lia.
        -- simpl. reflexivity.
Qed.