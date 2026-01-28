Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition get_positive_spec (l: list Z) (res: list Z) : Prop :=
  (forall x, In x res -> In x l /\ x > 0) /\
  (forall x, In x l -> x > 0 -> In x res).

Example test_get_positive : get_positive_spec [0; -1; -2; 0; -2; -1; -2; -3; -4; -5; -3; -2] [].
Proof.
  unfold get_positive_spec.
  split.
  - intros x H.
    inversion H.
  - intros x HIn HPos.
    simpl in HIn.
    repeat match goal with
    | [ H : _ \/ _ |- _ ] => destruct H as [H | H]; [ subst; lia | ]
    end.
    contradiction.
Qed.