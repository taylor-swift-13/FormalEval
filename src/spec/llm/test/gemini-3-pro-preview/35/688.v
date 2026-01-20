Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition max_element_spec (l : list R) (res : R) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [-4.5%R; -3.4%R; 5.6%R; 7.8%R; 1.9737820350258957%R; -9.0%R; 11.838575197213943%R; 1.9737820350258957%R; 1.9737820350258957%R] 11.838575197213943%R.
Proof.
  unfold max_element_spec.
  split.
  - simpl.
    do 6 right. left. reflexivity.
  - intros x H.
    simpl in H.
    repeat (destruct H as [H | H]; [subst; lra | ]).
    contradiction.
Qed.