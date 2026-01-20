Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition max_element_spec (l : list R) (res : R) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [1.2%R; -3.4%R; 1.2%R; 10.889126081885%R; -3.4%R; 5.6%R; 6.19089849046658%R; 17.742268880987826%R; 10.675343474768061%R; -9.0%R; 10.1%R; -9.0%R] 17.742268880987826%R.
Proof.
  unfold max_element_spec.
  split.
  - simpl.
    do 7 right. left. reflexivity.
  - intros x H.
    simpl in H.
    repeat (destruct H as [H | H]; [subst; lra | ]).
    contradiction.
Qed.