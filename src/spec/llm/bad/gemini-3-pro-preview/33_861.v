Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
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
  [300; 500; 6; 7; 290; 8; 289; 20; -7; -277; 104; 200; 3; 4; 700; 900; -901; 800; 1000; -901; 1000; 289] 
  [-277; 500; 6; 3; 290; 8; 7; 20; -7; 289; 104; 200; 289; 4; 700; 300; -901; 800; 900; -901; 1000; 1000].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      repeat (destruct i as [|i]; [ simpl in *; try (contradiction || reflexivity) | ]).
      reflexivity.
    + split.
      * simpl.
        repeat (eapply Permutation_Add; [ repeat (constructor || apply Add_cons) | ]).
        apply Permutation_nil.
      * simpl.
        repeat (apply Sorted_cons; [ constructor; try (apply Z.leb_le; reflexivity) | ]).
        apply Sorted_nil.
Qed.