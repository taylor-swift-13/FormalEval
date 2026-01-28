Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition max_element_spec (l : list nat) (m : nat) : Prop :=
  l <> [] /\
  In m l /\
  forall x, In x l -> x <= m.

Example test_max_element : max_element_spec [50; 49; 49; 100; 47; 46] 100.
Proof.
  unfold max_element_spec.
  repeat split.
  - (* Prove list is not empty *)
    discriminate.
  - (* Prove 100 is in the list *)
    simpl.
    repeat (try (left; reflexivity); right).
  - (* Prove all elements are <= 100 *)
    intros x H.
    simpl in H.
    repeat destruct H as [H | H]; try (rewrite H; lia).
    contradiction.
Qed.