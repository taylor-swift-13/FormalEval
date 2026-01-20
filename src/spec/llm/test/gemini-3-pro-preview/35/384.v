Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition max_element_spec (l : list R) (res : R) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [1.2; -3.4; 1.2; 81.6; 5.6; 17.742268880987826; 10.675343474768061; -9.0; 10.1] 81.6.
Proof.
  unfold max_element_spec.
  split.
  - (* Part 1: Prove 81.6 is in the list *)
    simpl.
    right. right. right. left. reflexivity.
  - (* Part 2: Prove for all x in the list, x <= 81.6 *)
    intros x H.
    simpl in H.
    repeat (destruct H as [H | H]; [ subst; lra | ]).
    contradiction.
Qed.