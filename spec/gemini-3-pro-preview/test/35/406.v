Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition max_element_spec (l : list R) (res : R) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [1.2; -3.4; 1.2; 5.958120335680599; 15.4; -3.4; -9.0; 10.1; 5.6] 15.4.
Proof.
  unfold max_element_spec.
  split.
  - simpl.
    do 4 right. left. reflexivity.
  - intros x H.
    simpl in H.
    repeat (destruct H as [H|H]; [subst; lra | ]).
    contradiction.
Qed.