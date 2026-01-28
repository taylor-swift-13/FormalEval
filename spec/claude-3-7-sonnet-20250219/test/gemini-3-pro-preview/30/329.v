Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition get_positive_spec (l: list Z) (res: list Z) : Prop :=
  (forall x, In x res -> In x l /\ x > 0) /\
  (forall x, In x l -> x > 0 -> In x res).

Example test_get_positive : get_positive_spec [2; 1; 1; 2; 1; 1] [2; 1; 1; 2; 1; 1].
Proof.
  unfold get_positive_spec.
  split.
  - intros x H.
    split.
    + assumption.
    + simpl in H.
      repeat destruct H as [H | H]; subst; lia.
  - intros x HIn HPos.
    assumption.
Qed.