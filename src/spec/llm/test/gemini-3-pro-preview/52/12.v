Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  res = true <-> (forall x, In x l -> x < t).

Example test_below_threshold: below_threshold_spec [1; 2; 3; 4] 4 false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H. inversion H.
  - intros H.
    (* We show that the hypothesis implies a contradiction because 4 is in the list but not < 4 *)
    specialize (H 4).
    assert (In 4 [1; 2; 3; 4]).
    { simpl. right. right. right. left. reflexivity. }
    apply H in H0.
    lia.
Qed.