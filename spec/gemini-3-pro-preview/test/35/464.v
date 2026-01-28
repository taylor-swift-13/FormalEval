Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition max_element_spec (l : list R) (res : R) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [1.2%R; -4.5%R; -3.4%R; 5.6%R; -9.0%R; 1.2%R; 1.2%R; -4.5%R; -9.0%R] 5.6%R.
Proof.
  unfold max_element_spec.
  split.
  - simpl. do 3 right. left. reflexivity.
  - intros x H.
    simpl in H.
    destruct H as [H | [H | [H | [H | [H | [H | [H | [H | [H | H]]]]]]]]]; subst; try lra; try contradiction.
Qed.