Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  res = true <-> (forall x, In x l -> x < t).

Example test_below_threshold: below_threshold_spec [100; 200; 300; 0; 0; 0; 0; 100; 0] 0 false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H. inversion H.
  - intros H.
    specialize (H 100).
    assert (In 100 [100; 200; 300; 0; 0; 0; 0; 100; 0]).
    { simpl. left. reflexivity. }
    apply H in H0.
    lia.
Qed.