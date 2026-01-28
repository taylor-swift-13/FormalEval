Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition get_positive_spec (l: list Z) (res: list Z) : Prop :=
  (forall x, In x res -> In x l /\ x > 0) /\
  (forall x, In x l -> x > 0 -> In x res).

Example test_get_positive : get_positive_spec [-1; -2; -5; -3; -4; 6; 0; 6; 7; -9; 10; 5; 10; -9] [6; 6; 7; 10; 5; 10].
Proof.
  unfold get_positive_spec.
  split.
  - intros x H.
    simpl in H.
    repeat match goal with
    | [ H : _ \/ _ |- _ ] => destruct H as [H|H]
    end; subst; try contradiction; split; try (simpl; tauto); try lia.
  - intros x HIn HPos.
    simpl in HIn.
    repeat match goal with
    | [ H : _ \/ _ |- _ ] => destruct H as [H|H]
    end; subst; try contradiction; try lia; simpl; tauto.
Qed.