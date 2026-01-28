Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Open Scope R_scope.

Definition get_positive_spec (l: list R) (res: list R) : Prop :=
  (forall x, In x res -> In x l /\ x > 0) /\
  (forall x, In x l -> x > 0 -> In x res).

Example test_get_positive : get_positive_spec [0; -1.25; -1.5; -0.75; -2.25; -1; -2; -3; -4; -5; -6; 0; 0] [].
Proof.
  unfold get_positive_spec.
  split.
  - intros x H.
    inversion H.
  - intros x HIn HPos.
    simpl in HIn.
    repeat (destruct HIn as [HIn | HIn]; [subst; lra | ]).
    contradiction.
Qed.