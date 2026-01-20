Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition max_element_spec (l : list R) (res : R) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [1.2; -3.4; 1.2; -11.39330787369553; -3.4; 5.6; 17.742268880987826; 10.675343474768061; -9.0; 10.1] 17.742268880987826.
Proof.
  unfold max_element_spec.
  split.
  - (* Part 1: Prove 17.742268880987826 is in the list *)
    simpl.
    right. right. right. right. right. right. left. reflexivity.
  - (* Part 2: Prove for all x in list, x <= 17.742268880987826 *)
    intros x H.
    simpl in H.
    destruct H as [H | H]; [subst; lra | ].
    destruct H as [H | H]; [subst; lra | ].
    destruct H as [H | H]; [subst; lra | ].
    destruct H as [H | H]; [subst; lra | ].
    destruct H as [H | H]; [subst; lra | ].
    destruct H as [H | H]; [subst; lra | ].
    destruct H as [H | H]; [subst; lra | ].
    destruct H as [H | H]; [subst; lra | ].
    destruct H as [H | H]; [subst; lra | ].
    destruct H as [H | H]; [subst; lra | ].
    contradiction.
Qed.