Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition get_positive_spec (l: list Z) (res: list Z) : Prop :=
  (forall x, In x res -> In x l /\ x > 0) /\
  (forall x, In x l -> x > 0 -> In x res).

Example test_get_positive : get_positive_spec [6; -5; -4; 8; 8; -2; -100; 6; -100; -1; -1; -5; -1; 8; -100] [6; 8; 8; 6; 8].
Proof.
  unfold get_positive_spec.
  split.
  - intros x H.
    simpl in H.
    repeat (destruct H as [H | H]; [subst; split; [simpl; tauto | lia] | ]).
    contradiction.
  - intros x HIn HPos.
    simpl in HIn.
    repeat (destruct HIn as [H | HIn]; [subst; try lia; simpl; tauto | ]).
    contradiction.
Qed.