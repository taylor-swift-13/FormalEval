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

Example test_case : sort_third_spec [9; 12; 15; 6; 3; 8; 13; 18; 7] [6; 12; 15; 9; 3; 8; 13; 18; 7].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* Check indices 0 to 8 explicitly *)
      do 9 (destruct i; [ simpl in H |- *; try congruence; reflexivity | ]).
      (* Indices >= 9 *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        (* Goal: Permutation [6; 9; 13] [9; 6; 13] *)
        simpl.
        apply perm_swap.
      * (* 4. Sortedness of extracted thirds *)
        (* Goal: Sorted Z.le [6; 9; 13] *)
        simpl.
        repeat (constructor; try (unfold Z.le; simpl; discriminate)).
Qed.