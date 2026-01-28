Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition max_element_spec (l : list R) (res : R) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [1.2; -4.5; -3.4; 5.6; 7.8; -9.0; 10.1; -12.3; 15.4; 20.5; -25.6; 30.7; -35.8; 40.9; -46.0; -8.601314347821834; 57.2; -63.3; 69.4; -75.5; 81.6; 11.393628605126539; 93.8; 99.9; 30.7; 20.5] 99.9.
Proof.
  unfold max_element_spec.
  split.
  - simpl.
    do 23 right. left. reflexivity.
  - intros x H.
    simpl in H.
    repeat (destruct H as [H | H]; [subst; lra | ]).
    contradiction.
Qed.