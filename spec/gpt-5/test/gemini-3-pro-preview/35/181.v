Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.

Import ListNotations.
Open Scope R_scope.

Definition max_element_spec (l : list R) (m : R) : Prop :=
  l <> nil /\ In m l /\ forall x, In x l -> x <= m.

Example test_max_element : max_element_spec [1.2; -3.4; 1.2; -3.4; 1.6651177816249232; 5.6; 15.4; -9.0; 10.902787118383477; -3.4] 15.4.
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
    repeat (destruct H as [H | H]; [subst; try lra | ]).
    contradiction.
Qed.