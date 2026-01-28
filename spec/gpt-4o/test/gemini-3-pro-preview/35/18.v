Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition max_element_spec (l : list nat) (max_elem : nat) : Prop :=
  In max_elem l /\ (forall x, In x l -> x <= max_elem).

Example test_max_element : max_element_spec [3; 1; 2; 9; 4; 5; 6; 7; 5] 9.
Proof.
  unfold max_element_spec.
  split.
  - (* Prove that 9 is in the list *)
    simpl.
    right. right. right. left. reflexivity.
  - (* Prove that for all x in the list, x <= 9 *)
    intros x H.
    simpl in H.
    repeat destruct H as [H | H]; try (rewrite H; lia).
    contradiction.
Qed.