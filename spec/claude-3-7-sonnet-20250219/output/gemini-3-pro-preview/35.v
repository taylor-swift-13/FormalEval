Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition max_element_spec (l : list nat) (m : nat) : Prop :=
  l <> [] /\
  In m l /\
  forall x, In x l -> x <= m.

Example test_max_element : max_element_spec [1; 2; 3] 3.
Proof.
  unfold max_element_spec.
  repeat split.
  - (* Prove list is not empty *)
    discriminate.
  - (* Prove 3 is in [1; 2; 3] *)
    simpl.
    repeat (try (left; reflexivity); right).
  - (* Prove all elements are <= 3 *)
    intros x H.
    simpl in H.
    destruct H as [H1 | [H2 | [H3 | H4]]].
    + (* x = 1 *)
      rewrite H1. lia.
    + (* x = 2 *)
      rewrite H2. lia.
    + (* x = 3 *)
      rewrite H3. lia.
    + (* End of list *)
      contradiction.
Qed.