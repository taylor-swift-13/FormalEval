Require Import List.
Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold :
  below_threshold_spec (-5 :: -4 :: -3 :: nil) (-6) false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H. discriminate H.
  - intros H.
    exfalso.
    assert (In (-5) (-5 :: -4 :: -3 :: nil)) as Hin.
    { simpl. left. reflexivity. }
    specialize (H (-5) Hin).
    lia.
Qed.