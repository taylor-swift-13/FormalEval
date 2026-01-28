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
  [1; 2; 3; -3; 5; 1; -8; 16; 16; -8; 14; 9; -12; 7; 6; -12] 
  [-12; 2; 3; -12; 5; 1; -8; 16; 16; -8; 14; 9; -3; 7; 6; 1].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* We destruct i 16 times to cover the list length explicitly *)
      do 16 (destruct i; [ 
        simpl in *; 
        try congruence; (* Solves cases where i mod 3 = 0 via hypothesis H *)
        reflexivity     (* Solves cases where values match *)
      | ]).
      (* Case i >= 16 *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* The output extracted thirds are exactly the reverse of the input extracted thirds *)
        apply Permutation_rev.
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat (constructor; try lia).
Qed.