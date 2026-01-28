Require Import List ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition problem_9_spec (input output : list Z) :=
  length output = length input /\
  forall i,
    (i < length output)%nat ->
    (forall j, (j <= i)%nat -> nth j input 0 <= nth i output 0) /\
    (exists j, (j <= i)%nat /\ nth j input 0 = nth i output 0).

Example test_all_equal : problem_9_spec [[4%Z; 3%Z; 2%Z; 1%Z]] [4%Z; 4%Z; 4%Z; 4%Z].
Proof.
  unfold problem_9_spec.
  split.
  - reflexivity.
  - intros i H.
    simpl in H.
    (* Both lists are of length 1, 2, 3 or 4; since length input = 1 *)
    destruct input as [h] | [h1 h2] | [h1 h2 h3] | [h1 h2 h3 h4]; simpl in H; try lia.
    + (* input length = 1 *)
      destruct i; simpl in *; lia.
    + (* input length >= 2, but input list has length 1? Impossible, so input list length must be 1 *)
      lia.
Qed.