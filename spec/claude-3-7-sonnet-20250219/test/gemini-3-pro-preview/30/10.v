Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition get_positive_spec (l: list Z) (res: list Z) : Prop :=
  (forall x, In x res -> In x l /\ x > 0) /\
  (forall x, In x l -> x > 0 -> In x res).

Example test_get_positive : get_positive_spec [-5; -4; -1; 0; 1; 4; 5] [1; 4; 5].
Proof.
  unfold get_positive_spec.
  split.
  - intros x H.
    simpl in H.
    destruct H as [H | [H | [H | H]]]; subst.
    + split.
      * simpl; tauto.
      * lia.
    + split.
      * simpl; tauto.
      * lia.
    + split.
      * simpl; tauto.
      * lia.
    + contradiction.
  - intros x HIn HPos.
    simpl in HIn.
    destruct HIn as [H | [H | [H | [H | [H | [H | [H | H]]]]]]]; subst.
    + lia.
    + lia.
    + lia.
    + lia.
    + simpl; tauto.
    + simpl; tauto.
    + simpl; tauto.
    + contradiction.
Qed.