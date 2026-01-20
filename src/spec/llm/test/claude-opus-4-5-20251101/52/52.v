Require Import List.
Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold :
  below_threshold_spec (1 :: 20 :: 4 :: 10 :: nil) (-4) false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H.
    discriminate H.
  - intros H.
    exfalso.
    assert (In 1 (1 :: 20 :: 4 :: 10 :: nil)) as Hin.
    { simpl. left. reflexivity. }
    specialize (H 1 Hin).
    lia.
Qed.