Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition max_element_spec (l : list nat) (m : nat) : Prop :=
  l <> [] /\
  In m l /\
  forall x, In x l -> x <= m.

Example test_max_element : max_element_spec [99] 99.
Proof.
  unfold max_element_spec.
  repeat split.
  - discriminate.
  - simpl.
    left. reflexivity.
  - intros x H.
    simpl in H.
    destruct H as [H1 | H2].
    + rewrite H1. lia.
    + contradiction.
Qed.