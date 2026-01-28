Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition max_element_spec (l : list nat) (m : nat) : Prop :=
  l <> [] /\
  In m l /\
  forall x, In x l -> x <= m.

Example test_max_element : max_element_spec [8; 7; 6; 5; 4; 3] 8.
Proof.
  unfold max_element_spec.
  repeat split.
  - (* Prove list is not empty *)
    discriminate.
  - (* Prove 8 is in [8; 7; 6; 5; 4; 3] *)
    simpl.
    repeat (try (left; reflexivity); right).
  - (* Prove all elements are <= 8 *)
    intros x H.
    simpl in H.
    destruct H as [H1 | [H2 | [H3 | [H4 | [H5 | [H6 | H7]]]]]].
    + (* x = 8 *)
      rewrite H1. lia.
    + (* x = 7 *)
      rewrite H2. lia.
    + (* x = 6 *)
      rewrite H3. lia.
    + (* x = 5 *)
      rewrite H4. lia.
    + (* x = 4 *)
      rewrite H5. lia.
    + (* x = 3 *)
      rewrite H6. lia.
    + (* End of list *)
      contradiction.
Qed.