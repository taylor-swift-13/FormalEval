Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition max_element_spec (l : list nat) (max_elem : nat) : Prop :=
  In max_elem l /\ (forall x, In x l -> x <= max_elem).

Example test_max_element : max_element_spec [8; 6; 6; 4; 6; 3] 8.
Proof.
  unfold max_element_spec.
  split.
  - simpl.
    left. reflexivity.
  - intros x H.
    simpl in H.
    destruct H as [H1 | [H2 | [H3 | [H4 | [H5 | [H6 | H7]]]]]].
    + rewrite H1. lia.
    + rewrite H2. lia.
    + rewrite H3. lia.
    + rewrite H4. lia.
    + rewrite H5. lia.
    + rewrite H6. lia.
    + contradiction.
Qed.