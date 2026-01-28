Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.

Import ListNotations.
Open Scope R_scope.

Definition max_element_spec (l : list R) (m : R) : Prop :=
  l <> nil /\ In m l /\ forall x, In x l -> x <= m.

Example test_max_element : max_element_spec [1.2; -4.5; -3.4; 5.6; -9.0; 1.2; 1.2; -4.5] 5.6.
Proof.
  unfold max_element_spec.
  repeat split.
  - (* Case 1: l <> nil *)
    discriminate.
  - (* Case 2: In m l *)
    simpl.
    right. right. right. left. reflexivity.
  - (* Case 3: forall x, In x l -> x <= m *)
    intros x H.
    simpl in H.
    repeat (destruct H as [H | H]; [subst; lra | ]).
    contradiction.
Qed.