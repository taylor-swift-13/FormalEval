Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition max_element_spec (l : list R) (res : R) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [1.2; -3.4; 1.2; -3.4; 5.6; 69.4; -9.0; 10.1] 69.4.
Proof.
  unfold max_element_spec.
  split.
  - simpl.
    do 5 right. left. reflexivity.
  - intros x H.
    simpl in H.
    repeat match goal with
    | [ H : _ \/ _ |- _ ] => destruct H as [H | H]
    end; subst; try lra.
    contradiction.
Qed.