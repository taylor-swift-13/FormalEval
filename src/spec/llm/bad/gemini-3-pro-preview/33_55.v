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
  [3; 1; 2; 3; 4; 5; 6; 7; 45; 9; 12; 14; 15; 21; 3; 13] 
  [3; 1; 2; 3; 4; 5; 6; 7; 45; 9; 12; 14; 13; 21; 3; 15].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* Check indices 0 to 16. If i >= 16, both are None. *)
      do 17 (destruct i; [ simpl in *; try (contradiction || reflexivity) | ]).
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* Lists are identical except last two elements [..., 13, 15] vs [..., 15, 13] *)
        repeat apply perm_skip.
        apply perm_swap.
        apply perm_nil.
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat (constructor; try (compute; congruence)).
Qed.