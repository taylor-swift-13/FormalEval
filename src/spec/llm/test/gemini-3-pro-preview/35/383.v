Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition max_element_spec (l : list R) (res : R) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [1.2; -4.5; -46.0; 17.742268880987826; 11.01793702200241; 7.8; -9.0; 10.1; 10.1; 10.1] 17.742268880987826.
Proof.
  unfold max_element_spec.
  split.
  - repeat (first [left; reflexivity | right]).
  - intros x H.
    repeat (destruct H as [H | H]; [ subst; lra | ]).
    contradiction.
Qed.