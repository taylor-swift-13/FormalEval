Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold : below_threshold_spec [3%Z; 1%Z; 4%Z; 7%Z; 10%Z; 7%Z] 6%Z false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H.
    discriminate H.
  - intros H.
    assert (HIn: In 7%Z [3%Z; 1%Z; 4%Z; 7%Z; 10%Z; 7%Z]).
    { simpl. right. right. right. left. reflexivity. }
    apply H in HIn.
    lia.
Qed.