Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition max_element_spec (l : list R) (res : R) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [1.2%R; 1.3749746958929525%R; -4.5%R; -3.4%R; 4.842879905706559%R; 7.8%R; -9.0%R; 10.1%R; 1.2%R; -4.5%R] 10.1%R.
Proof.
  unfold max_element_spec.
  split.
  - (* Part 1: Prove 10.1%R is in the list *)
    simpl.
    do 7 right. left. reflexivity.
  - (* Part 2: Prove for all x in list, x <= 10.1%R *)
    intros x H.
    simpl in H.
    repeat (destruct H as [H | H]; [subst; lra | ]).
    contradiction.
Qed.