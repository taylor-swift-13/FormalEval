Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition get_positive_spec (l: list Z) (res: list Z) : Prop :=
  (forall x, In x res -> In x l /\ x > 0) /\
  (forall x, In x l -> x > 0 -> In x res).

Example test_get_positive : get_positive_spec [1; 1; 1; -8; 1; 1; 2; 2; 2; 2; 2; 2; 2] [1; 1; 1; 1; 1; 2; 2; 2; 2; 2; 2; 2].
Proof.
  unfold get_positive_spec.
  split.
  - intros x H.
    simpl in H.
    repeat (destruct H as [H|H]; [ subst; split; [ simpl; tauto | lia ] | idtac ]).
    contradiction.
  - intros x H Hpos.
    simpl in H.
    repeat (destruct H as [H|H]; [ subst; try lia; simpl; tauto | idtac ]).
    contradiction.
Qed.