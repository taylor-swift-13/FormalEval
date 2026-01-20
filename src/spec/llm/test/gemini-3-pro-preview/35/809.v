Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition max_element_spec (l : list R) (res : R) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [1.2; -4.5; -3.4; 5.6; -21.001516927331863; 4.977938453667969; 7.8; -9.0; 10.1; -12.3; 15.4; 20.5; -34.08965445380225; 30.7; -35.8; 40.9; -46.0; 51.1; 57.2; -63.3; 69.4; -75.5; -87.7; 93.8; 99.9; 7.8] 99.9.
Proof.
  unfold max_element_spec.
  split.
  - (* Part 1: Prove 99.9 is in the list *)
    simpl.
    (* 99.9 is at index 24 (0-based) in the list *)
    do 24 right. left. reflexivity.
  - (* Part 2: Prove for all x in list, x <= 99.9 *)
    intros x H.
    simpl in H.
    (* Break down the large disjunction of equalities *)
    repeat (match goal with
            | [ H : _ \/ _ |- _ ] => destruct H as [H | H]
            end; [ subst; lra | ]).
    (* Handle the final case (contradiction from False) or last element *)
    contradiction.
Qed.