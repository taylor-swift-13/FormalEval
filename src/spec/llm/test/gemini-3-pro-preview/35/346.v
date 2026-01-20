Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition max_element_spec (l : list R) (res : R) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [1.2; -4.5; -3.4; -46.0; 17.742268880987826; 5.6; 7.8; 77.07852302260174; 10.1; 7.8; 10.1] 77.07852302260174.
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