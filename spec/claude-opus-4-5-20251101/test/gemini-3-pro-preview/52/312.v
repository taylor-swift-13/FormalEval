Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold : below_threshold_spec [100%Z; 9999999%Z; -400%Z; 19%Z] 8000000%Z false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H.
    discriminate.
  - intros H.
    assert (HIn : In 9999999%Z [100%Z; 9999999%Z; -400%Z; 19%Z]).
    { simpl. right. left. reflexivity. }
    apply H in HIn.
    lia.
Qed.