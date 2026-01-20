Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Import ListNotations.

Definition max_element_spec (l : list nat) (max_elem : nat) : Prop :=
  In max_elem l /\ (forall x, In x l -> x <= max_elem).

Example test_max_element : max_element_spec [1; 2; 3] 3.
Proof.
  unfold max_element_spec.
  split.
  - (* Prove In 3 [1; 2; 3] *)
    simpl. right. right. left. reflexivity.
  - (* Prove forall x, In x [1; 2; 3] -> x <= 3 *)
    intros x H.
    simpl in H.
    destruct H as [H | [H | [H | H]]].
    + rewrite H. auto.
    + rewrite H. auto.
    + rewrite H. auto.
    + contradiction.
Qed.