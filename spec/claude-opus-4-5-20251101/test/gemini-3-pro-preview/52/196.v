Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold : below_threshold_spec [10000000%Z; 9000000%Z; 1998%Z; 8000000%Z; 7000000%Z; 6000000%Z; 2000000%Z] 100%Z false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H. discriminate.
  - intros H.
    specialize (H 10000000%Z).
    assert (In 10000000%Z [10000000%Z; 9000000%Z; 1998%Z; 8000000%Z; 7000000%Z; 6000000%Z; 2000000%Z]).
    { simpl. left. reflexivity. }
    apply H in H0.
    lia.
Qed.