Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition max_element_spec (l : list R) (res : R) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [-4.5; 30.7; -3.4; -68.11296101258709; 5.6; 7.8; -9.0; 10.1; -12.3; 15.4; 20.5; 30.7; -35.8; 40.9; 20.5; -46.0; 51.1; 57.2; -63.3; 20.793566236740514; 69.4; 30.7; -75.5; 81.6; -68.11296101258709; -87.7; 93.8; 20.793566236740514] 93.8.
Proof.
  unfold max_element_spec.
  split.
  - simpl.
    repeat (try (left; reflexivity); right).
  - intros x H.
    simpl in H.
    repeat match goal with
           | [ H : _ \/ _ |- _ ] => destruct H as [H | H]; [ subst; lra | ]
           end.
    contradiction.
Qed.