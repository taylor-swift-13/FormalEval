Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition max_element_spec (l : list nat) (max_elem : nat) : Prop :=
  In max_elem l /\ (forall x, In x l -> x <= max_elem).

Example test_max_element : max_element_spec [8; 7; 6; 5; 4; 3] 8.
Proof.
  unfold max_element_spec.
  split.
  - simpl.
    left. reflexivity.
  - intros x H.
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