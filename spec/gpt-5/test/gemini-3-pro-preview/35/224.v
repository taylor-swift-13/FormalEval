Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.

Import ListNotations.
Open Scope R_scope.

Definition max_element_spec (l : list R) (m : R) : Prop :=
  l <> nil /\ In m l /\ forall x, In x l -> x <= m.

Example test_max_element : max_element_spec [1.2%R; -3.4%R; 1.2%R; -3.4%R; 5.6%R; -3.4%R; 17.742268880987826%R; -9.0%R; 11.393628605126539%R] 17.742268880987826%R.
Proof.
  unfold max_element_spec.
  repeat split.
  - (* Case 1: l <> nil *)
    discriminate.
  - (* Case 2: In m l *)
    simpl.
    do 6 right. left. reflexivity.
  - (* Case 3: forall x, In x l -> x <= m *)
    intros x H.
    simpl in H.
    repeat destruct H as [H | H]; subst; try lra.
Qed.