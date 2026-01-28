Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition get_positive_spec (l: list Z) (res: list Z) : Prop :=
  (forall x, In x res -> In x l /\ x > 0) /\
  (forall x, In x l -> x > 0 -> In x res).

Example test_get_positive : get_positive_spec [1; 2; 3; -4; -2; 0; -3; 6; -9; -5; 10] [1; 2; 3; 6; 10].
Proof.
  unfold get_positive_spec.
  split.
  - intros x H.
    repeat (destruct H as [H | H]; [subst; split; [simpl; tauto | lia] | ]).
    contradiction.
  - intros x HIn HPos.
    repeat (destruct HIn as [HIn | HIn]; [subst; simpl; try tauto; try lia | ]).
    contradiction.
Qed.