Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition max_element_spec (l : list R) (res : R) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [1.2%R; -8.483231457866996%R; -3.4%R; 1.2%R; 5.6%R; 15.4%R; -9.0%R; 10.1%R; 15.4%R; 5.6%R; 1.2%R; 5.6%R] 15.4%R.
Proof.
  unfold max_element_spec.
  split.
  - (* Part 1: Prove 15.4 is in the list *)
    simpl.
    do 5 right. left. reflexivity.
  - (* Part 2: Prove for all x in the list, x <= 15.4 *)
    intros x H.
    simpl in H.
    repeat (destruct H as [H | H]; [subst; lra | ]).
    contradiction.
Qed.