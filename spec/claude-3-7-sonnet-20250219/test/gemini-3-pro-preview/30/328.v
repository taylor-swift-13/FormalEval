Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition get_positive_spec (l: list Z) (res: list Z) : Prop :=
  (forall x, In x res -> In x l /\ x > 0) /\
  (forall x, In x l -> x > 0 -> In x res).

Example test_get_positive : get_positive_spec [0; 1; 2; -4; -3; -5; 0; 0; 6; 7; -10; 10; 10; 1; 10; 6; 6] [1; 2; 6; 7; 10; 10; 1; 10; 6; 6].
Proof.
  unfold get_positive_spec.
  split.
  - intros x H.
    simpl in H.
    repeat (destruct H as [H | H]; [ subst; split; [ simpl; tauto | lia ] | idtac ]).
    contradiction.
  - intros x H HPos.
    simpl in H.
    repeat (destruct H as [H | H]; [ subst; try lia; simpl; tauto | idtac ]).
    contradiction.
Qed.