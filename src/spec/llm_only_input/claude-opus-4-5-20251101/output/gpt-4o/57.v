Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Import ListNotations.

Definition monotonic_spec (l : list nat) (result : bool) : Prop :=
  result = true <-> 
    (forall i j, i < j < length l -> nth i l 0 <= nth j l 0) \/
    (forall i j, i < j < length l -> nth i l 0 >= nth j l 0).

(* The test case uses Z integers, but the spec uses nat. 
   We'll work with the nat version as specified. *)
Definition test_input : list nat := [1; 2; 4; 10].

Example monotonic_test : monotonic_spec test_input true.
Proof.
  unfold monotonic_spec, test_input.
  split.
  - intros _.
    left.
    intros i j [Hij Hj].
    simpl in Hj.
    destruct i as [|[|[|[|i']]]]; destruct j as [|[|[|[|j']]]]; simpl; try lia.
  - intros _. reflexivity.
Qed.