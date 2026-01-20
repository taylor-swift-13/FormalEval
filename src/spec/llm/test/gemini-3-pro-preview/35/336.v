Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition max_element_spec (l : list R) (res : R) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [1.2%R; 1.3749746958929525%R; -4.5%R; 0.6809434700413334%R; 7.8%R; -9.0%R; 10.1%R; 1.2%R; 10.1%R; 10.1%R] 10.1%R.
Proof.
  unfold max_element_spec.
  split.
  - simpl.
    do 6 right. left. reflexivity.
  - intros x H.
    simpl in H.
    repeat (destruct H as [H | H]; [ subst; lra | ]).
    contradiction.
Qed.