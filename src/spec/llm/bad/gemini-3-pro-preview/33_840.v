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
  [-4; 7; 3; -6; 3; 0; -8; 6; 2; 0; 1; 8; -6] 
  [-8; 7; 3; -6; 3; 0; -6; 6; 2; -4; 1; 8; 0].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* Check for i = 0 to 12. For i >= 13, both are None. *)
      do 13 (destruct i; [ simpl in H; try contradiction; simpl; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* LHS: [-8; -6; -6; -4; 0] *)
        (* RHS: [-4; -6; -8; 0; -6] *)
        apply Permutation_cons_app with (l1 := [-4; -6]) (l2 := [0; -6]). simpl.
        apply Permutation_cons_app with (l1 := [-4]) (l2 := [0; -6]). simpl.
        apply Permutation_cons_app with (l1 := [-4; 0]) (l2 := []). simpl.
        apply Permutation_refl.
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat (apply Sorted_cons; [| constructor; try lia ]).
        apply Sorted_nil.
Qed.