Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.

Import ListNotations.
Open Scope R_scope.

Definition max_element_spec (l : list R) (m : R) : Prop :=
  l <> nil /\ In m l /\ forall x, In x l -> x <= m.

Example test_max_element : max_element_spec [1.2; -3.4; 81.6; 1.2; -3.4; 5.6; 15.4; -9.0; 99.9; 10.1] 99.9.
Proof.
  unfold max_element_spec.
  repeat split.
  - 
    discriminate.
  - 
    simpl.
    do 8 right. left. reflexivity.
  - 
    intros x H.
    simpl in H.
    repeat (destruct H as [H | H]; [ subst; lra | ]).
    contradiction.
Qed.