Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold : below_threshold_spec [1000; 500; 250; 125; 6; 62; 31; 31; 100] 499 false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H. inversion H.
  - intros H.
    specialize (H 1000).
    assert (In 1000 [1000; 500; 250; 125; 6; 62; 31; 31; 100]).
    { simpl. left. reflexivity. }
    apply H in H0.
    lia.
Qed.