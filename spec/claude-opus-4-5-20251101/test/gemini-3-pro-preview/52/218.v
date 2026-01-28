Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold : below_threshold_spec [2000000%Z; 10000000%Z; 9000000%Z; 10%Z; 8000000%Z; 6000000%Z; 2000%Z; 8000000%Z] 7000001%Z false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H. discriminate.
  - intros H.
    assert (Hin: In 10000000 [2000000; 10000000; 9000000; 10; 8000000; 6000000; 2000; 8000000]).
    { simpl. right. left. reflexivity. }
    specialize (H 10000000 Hin).
    lia.
Qed.