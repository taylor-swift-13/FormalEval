Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition max_element_spec (l : list R) (res : R) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [1.2%R; -3.4%R; 81.6%R; 1.2%R; -3.4%R; 10.675343474768061%R; 15.4%R; -9.0%R; 99.9%R; 9.135389490896912%R] 99.9%R.
Proof.
  unfold max_element_spec.
  split.
  - simpl.
    do 8 right. left. reflexivity.
  - intros x H.
    simpl in H.
    repeat (destruct H as [H | H]; [subst; lra | ]).
    contradiction.
Qed.