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

Example test_case : sort_third_spec [9; 12; 15; 6; 3; 8; 10; 23; 7; 23] [6; 12; 15; 9; 3; 8; 10; 23; 7; 23].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* We destruct i enough times to cover the list length (10 elements) *)
      do 10 (destruct i; [
        (* For each specific index 0..9: *)
        (* If i mod 3 == 0, then H (i mod 3 <> 0) is a contradiction *)
        try (exfalso; apply H; reflexivity);
        (* If i mod 3 != 0, we check nth_error equality *)
        try reflexivity
      | ]).
      (* For i >= 10, both lists return None *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        (* Extracted inputs: [9; 6; 10; 23] *)
        (* Extracted outputs: [6; 9; 10; 23] *)
        simpl.
        apply perm_swap.
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        (* Check sortedness of [6; 9; 10; 23] *)
        repeat (constructor; try (compute; discriminate)).
Qed.