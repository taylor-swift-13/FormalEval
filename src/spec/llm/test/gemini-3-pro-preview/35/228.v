Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition max_element_spec (l : list R) (res : R) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [8.95595695919447; -3.4; 1.2; 5.6; -9.0; 10.1; 15.4; 5.6] 15.4.
Proof.
  unfold max_element_spec.
  split.
  - simpl.
    right. right. right. right. right. right. left. reflexivity.
  - intros x H.
    simpl in H.
    repeat (destruct H as [H | H]; [subst; lra | ]).
    contradiction.
Qed.