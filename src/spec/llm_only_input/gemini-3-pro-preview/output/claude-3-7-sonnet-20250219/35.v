Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition max_element_spec (l : list nat) (m : nat) : Prop :=
  l <> [] /\
  In m l /\
  forall x, In x l -> x <= m.

Example test_max_element: max_element_spec [1; 2; 3] 3.
Proof.
  unfold max_element_spec.
  repeat split.
  - (* Prove the list is not empty *)
    discriminate.
  - (* Prove 3 is in the list *)
    simpl. auto.
  - (* Prove 3 is the maximum element *)
    intros x H.
    simpl in H.
    destruct H as [H | [H | [H | H]]].
    + subst. lia.
    + subst. lia.
    + subst. lia.
    + contradiction.
Qed.