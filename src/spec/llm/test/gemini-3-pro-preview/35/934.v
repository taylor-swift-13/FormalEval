Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition max_element_spec (l : list R) (res : R) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [4.977938453667969; 1.2; -4.5; -3.4; 5.6; 7.8; -9.0; 10.1; -12.3; -25.6; -2.1544108467456975; -68.11296101258709; -35.8; 40.9; -46.0; 51.1; 57.2; -63.3; 69.4; -75.5; -87.7; 93.8; 124.5611385860338; -4.5] 124.5611385860338.
Proof.
  unfold max_element_spec.
  split.
  - simpl.
    do 22 right. left. reflexivity.
  - intros x H.
    simpl in H.
    repeat (destruct H as [H | H]; [subst; lra | ]).
    contradiction.
Qed.