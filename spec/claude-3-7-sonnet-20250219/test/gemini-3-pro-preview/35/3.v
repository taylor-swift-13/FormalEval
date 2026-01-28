Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition max_element_spec (l : list nat) (m : nat) : Prop :=
  l <> [] /\
  In m l /\
  forall x, In x l -> x <= m.

Example test_max_element : max_element_spec [0; 0; 0; 0] 0.
Proof.
  unfold max_element_spec.
  repeat split.
  - discriminate.
  - simpl.
    repeat (try (left; reflexivity); right).
  - intros x H.
    simpl in H.
    destruct H as [H1 | [H2 | [H3 | [H4 | H5]]]].
    + rewrite H1. lia.
    + rewrite H2. lia.
    + rewrite H3. lia.
    + rewrite H4. lia.
    + contradiction.
Qed.