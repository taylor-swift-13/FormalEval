Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition max_element_spec (l : list nat) (m : nat) : Prop :=
  l <> [] /\
  In m l /\
  forall x, In x l -> x <= m.

Example test_max_element : max_element_spec [1; 2; 9; 5; 5; 6; 7; 7] 9.
Proof.
  unfold max_element_spec.
  repeat split.
  - discriminate.
  - simpl.
    repeat (try (left; reflexivity); right).
  - intros x H.
    simpl in H.
    repeat (destruct H as [H | H]; [ rewrite H; lia | ]).
    contradiction.
Qed.