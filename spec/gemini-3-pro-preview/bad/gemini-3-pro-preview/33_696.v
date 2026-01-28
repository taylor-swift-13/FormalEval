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
  [300; 6; 7; 290; 8; 289; 20; -105; -277; 104; 200; 3; 4; -9; 700; 900; -901; 800; 1000; -901; 104; 899; 17; 3] 
  [4; 6; 7; 20; 8; 289; 104; -105; -277; 290; 200; 3; 300; -9; 700; 899; -901; 800; 900; -901; 104; 1000; 17; 3].
Proof.
  unfold sort_third_spec.
  repeat split.
  - simpl. reflexivity.
  - intros i H.
    do 30 (destruct i as [|i]; [ simpl in *; try (elim H; fail); reflexivity | ]).
    simpl; reflexivity.
  - simpl.
    repeat (apply Permutation_Add; [ solve [ repeat constructor ] | ]).
    apply Permutation_nil.
  - simpl.
    repeat (constructor; try (cbv; discriminate)).
Qed.