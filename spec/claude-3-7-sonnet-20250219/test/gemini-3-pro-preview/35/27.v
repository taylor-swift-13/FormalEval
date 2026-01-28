Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition max_element_spec (l : list nat) (m : nat) : Prop :=
  l <> [] /\
  In m l /\
  forall x, In x l -> x <= m.

Example test_max_element : max_element_spec [101; 100; 100; 100] 101.
Proof.
  unfold max_element_spec.
  repeat split.
  - (* Prove list is not empty *)
    discriminate.
  - (* Prove 101 is in [101; 100; 100; 100] *)
    simpl.
    repeat (try (left; reflexivity); right).
  - (* Prove all elements are <= 101 *)
    intros x H.
    simpl in H.
    destruct H as [H1 | [H2 | [H3 | [H4 | H5]]]].
    + (* x = 101 *)
      rewrite H1. lia.
    + (* x = 100 *)
      rewrite H2. lia.
    + (* x = 100 *)
      rewrite H3. lia.
    + (* x = 100 *)
      rewrite H4. lia.
    + (* End of list *)
      contradiction.
Qed.