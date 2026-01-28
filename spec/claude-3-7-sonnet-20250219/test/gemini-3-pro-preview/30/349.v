Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition get_positive_spec (l: list Z) (res: list Z) : Prop :=
  (forall x, In x res -> In x l /\ x > 0) /\
  (forall x, In x l -> x > 0 -> In x res).

Example test_get_positive : get_positive_spec [-5; -5; -3; -4; 6; 6; 5; 7; -9; 10; 7; -4; -1] [6; 6; 5; 7; 10; 7].
Proof.
  unfold get_positive_spec.
  split.
  - intros x H.
    simpl in H.
    repeat destruct H as [H | H]; subst; try (split; [simpl; tauto | lia]); try contradiction.
  - intros x HIn HPos.
    simpl in HIn.
    repeat destruct HIn as [HIn | HIn]; subst; try lia; try (simpl; tauto); try contradiction.
Qed.