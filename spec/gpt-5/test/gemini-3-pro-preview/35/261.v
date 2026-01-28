Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.

Import ListNotations.
Open Scope R_scope.

Definition max_element_spec (l : list R) (m : R) : Prop :=
  l <> nil /\ In m l /\ forall x, In x l -> x <= m.

Example test_max_element : max_element_spec [1.2; -4.5; -3.4; 5.6; 7.8; -9.0; 10.1; -12.3; 15.4; 20.5; -25.6; 30.7; 7.8; -35.8; 40.9; -46.0; 51.1; 57.2; -63.3; 69.4; -75.5; 81.6; -87.7; 93.8; 99.9] 99.9.
Proof.
  unfold max_element_spec.
  repeat split.
  - (* Case 1: l <> nil *)
    discriminate.
  - (* Case 2: In m l *)
    simpl.
    repeat (try (left; reflexivity); right).
  - (* Case 3: forall x, In x l -> x <= m *)
    intros x H.
    simpl in H.
    repeat (destruct H as [H|H]; [subst; lra | ]).
    contradiction.
Qed.