Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition max_element_spec (l : list R) (res : R) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [1.2; -12.22100463885235; -3.4; 81.6; -3.948645877240116; 1.2; -3.4; 5.6; 15.4; -9.0; 9.135389490896912] 81.6.
Proof.
  unfold max_element_spec.
  split.
  - simpl.
    right. right. right. left. reflexivity.
  - intros x H.
    simpl in H.
    repeat (destruct H as [H | H]; [subst; lra | ]).
    contradiction.
Qed.