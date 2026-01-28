Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition max_element_spec (l : list nat) (m : nat) : Prop :=
  l <> [] /\
  In m l /\
  forall x, In x l -> x <= m.

Example test_max_element : max_element_spec [3; 1; 2; 9; 4; 5; 6; 7; 5] 9.
Proof.
  unfold max_element_spec.
  repeat split.
  - (* Prove list is not empty *)
    discriminate.
  - (* Prove 9 is in the list *)
    simpl.
    repeat (try (left; reflexivity); right).
  - (* Prove all elements are <= 9 *)
    intros x H.
    simpl in H.
    repeat destruct H as [H | H]; try (rewrite H; lia); try contradiction.
Qed.