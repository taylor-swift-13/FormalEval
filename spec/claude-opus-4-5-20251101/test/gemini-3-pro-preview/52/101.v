Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold : below_threshold_spec [100%Z; -200%Z; 300%Z; -400%Z; 500%Z; -600%Z] 100%Z false.
Proof.
  unfold below_threshold_spec.
  split.
  - (* Direction: false = true -> ... *)
    intros H.
    discriminate.
  - (* Direction: (forall x, In x ... -> x < 100) -> false = true *)
    intros H.
    (* We demonstrate a contradiction by showing an element exists that is not < 100 *)
    specialize (H 100%Z).
    assert (HIn : In 100%Z [100%Z; -200%Z; 300%Z; -400%Z; 500%Z; -600%Z]).
    { simpl. left. reflexivity. }
    apply H in HIn.
    (* HIn says 100 < 100, which is false *)
    lia.
Qed.