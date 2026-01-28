Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Fixpoint extract_thirds (l : list Z) (i : nat) : list Z :=
  match l with
  | [] => []
  | x :: xs => 
      if (i mod 3 =? 0)%nat 
      then x :: extract_thirds xs (S i) 
      else extract_thirds xs (S i)
  end.

Definition sort_third_spec (l : list Z) (res : list Z) : Prop :=
  length res = length l /\
  (forall i : nat, (i mod 3 <> 0)%nat -> nth_error res i = nth_error l i) /\
  Permutation (extract_thirds res 0) (extract_thirds l 0) /\
  Sorted Z.le (extract_thirds res 0).

Example test_case : sort_third_spec 
  [300; 500; 6; 7; 290; 8; 289; 20; -105; -277; 104; 200; 3; 4; 700; 900; -901; 800; 1000; 104]
  [-277; 500; 6; 3; 290; 8; 7; 20; -105; 289; 104; 200; 300; 4; 700; 900; -901; 800; 1000; 104].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 21 (destruct i; [
        simpl in *;
        try (match goal with | H : (?x <> 0)%nat |- _ => 
             try (exfalso; apply H; reflexivity) end);
        try reflexivity
      | ]).
      simpl. reflexivity.
    + split.
      * simpl. apply NoDup_Permutation.
        -- repeat (constructor; [ simpl; intro H; repeat (destruct H; try lia) | ]).
           apply NoDup_nil.
        -- repeat (constructor; [ simpl; intro H; repeat (destruct H; try lia) | ]).
           apply NoDup_nil.
        -- intros x; split; intro H; simpl in *; tauto.
      * simpl.
        repeat (constructor; simpl; try lia).
Qed.