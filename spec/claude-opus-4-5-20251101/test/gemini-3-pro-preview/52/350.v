Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold : below_threshold_spec [100%Z; 200%Z; 300%Z; 0%Z; 0%Z; 0%Z; 0%Z; 100%Z] 0%Z false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H.
    discriminate H.
  - intros H.
    assert (HIn: In 100%Z [100%Z; 200%Z; 300%Z; 0%Z; 0%Z; 0%Z; 0%Z; 100%Z]).
    { simpl. left. reflexivity. }
    apply H in HIn.
    lia.
Qed.