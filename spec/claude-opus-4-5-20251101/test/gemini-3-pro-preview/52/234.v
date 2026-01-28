Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold : below_threshold_spec [100%Z; -200%Z; 0%Z; 500%Z; 300%Z] 9%Z false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H.
    discriminate H.
  - intros H.
    assert (In 100 [100; -200; 0; 500; 300]) as Hin.
    { simpl. left. reflexivity. }
    apply H in Hin.
    lia.
Qed.