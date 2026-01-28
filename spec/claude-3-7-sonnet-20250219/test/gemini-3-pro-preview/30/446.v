Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Open Scope R_scope.

Definition get_positive_spec (l: list R) (res: list R) : Prop :=
  (forall x, In x res -> In x l /\ x > 0) /\
  (forall x, In x l -> x > 0 -> In x res).

Example test_get_positive : get_positive_spec 
  [0.5; -4; 2.5; 5; -2.2; -8; -4; -7; 9.9; -11.18889279027017; -10.5; 2.5; 9.9] 
  [0.5; 2.5; 5; 9.9; 2.5; 9.9].
Proof.
  unfold get_positive_spec.
  split.
  - intros x H.
    simpl in H.
    repeat (destruct H as [H|H]; [subst; split; [simpl; auto 20 | lra] | ]).
    contradiction.
  - intros x HIn HPos.
    simpl in HIn.
    repeat (destruct HIn as [HIn|HIn]; [subst; try lra; try (simpl; auto 20) | ]).
    contradiction.
Qed.