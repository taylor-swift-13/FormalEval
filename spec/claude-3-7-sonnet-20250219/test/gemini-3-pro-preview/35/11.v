Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition max_element_spec (l : list nat) (m : nat) : Prop :=
  l <> [] /\
  In m l /\
  forall x, In x l -> x <= m.

Example test_max_element : max_element_spec [2; 2; 2; 1; 2; 2] 2.
Proof.
  unfold max_element_spec.
  repeat split.
  - (* Prove list is not empty *)
    discriminate.
  - (* Prove 2 is in [2; 2; 2; 1; 2; 2] *)
    simpl.
    repeat (try (left; reflexivity); right).
  - (* Prove all elements are <= 2 *)
    intros x H.
    simpl in H.
    destruct H as [H | [H | [H | [H | [H | [H | H]]]]]].
    + rewrite H. lia.
    + rewrite H. lia.
    + rewrite H. lia.
    + rewrite H. lia.
    + rewrite H. lia.
    + rewrite H. lia.
    + contradiction.
Qed.