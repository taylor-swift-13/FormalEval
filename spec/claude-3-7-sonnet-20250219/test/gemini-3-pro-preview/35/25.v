Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition max_element_spec (l : list nat) (m : nat) : Prop :=
  l <> [] /\
  In m l /\
  forall x, In x l -> x <= m.

Example test_max_element : max_element_spec [0; 50; 49; 49; 47] 50.
Proof.
  unfold max_element_spec.
  repeat split.
  - (* Prove list is not empty *)
    discriminate.
  - (* Prove 50 is in [0; 50; 49; 49; 47] *)
    simpl.
    repeat (try (left; reflexivity); right).
  - (* Prove all elements are <= 50 *)
    intros x H.
    simpl in H.
    destruct H as [H1 | [H2 | [H3 | [H4 | [H5 | H6]]]]].
    + (* x = 0 *)
      rewrite H1. lia.
    + (* x = 50 *)
      rewrite H2. lia.
    + (* x = 49 *)
      rewrite H3. lia.
    + (* x = 49 *)
      rewrite H4. lia.
    + (* x = 47 *)
      rewrite H5. lia.
    + (* End of list *)
      contradiction.
Qed.