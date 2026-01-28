Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.

Import ListNotations.
Open Scope R_scope.

Definition max_element_spec (l : list R) (m : R) : Prop :=
  l <> nil /\ In m l /\ forall x, In x l -> x <= m.

Example test_max_element : max_element_spec [1.3749746958929525; -4.5; -3.4; 5.6; 7.8; -7.710030265326744; -9.0; 10.1; -50.04662603741016] 10.1.
Proof.
  unfold max_element_spec.
  repeat split.
  - (* Case 1: l <> nil *)
    intro H. discriminate.
  - (* Case 2: In m l *)
    simpl.
    do 7 right. left. reflexivity.
  - (* Case 3: forall x, In x l -> x <= m *)
    intros x H.
    simpl in H.
    repeat destruct H as [H | H]; subst; try lra.
    contradiction.
Qed.