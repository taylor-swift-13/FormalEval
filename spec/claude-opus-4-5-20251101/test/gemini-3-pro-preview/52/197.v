Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold : below_threshold_spec [100%Z; 2000000%Z; 300%Z; -400%Z; 500%Z; -600%Z] (-2)%Z false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H.
    discriminate.
  - intros H.
    assert (HIn : In 100 [100; 2000000; 300; -400; 500; -600]).
    { simpl. left. reflexivity. }
    apply H in HIn.
    lia.
Qed.