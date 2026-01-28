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
  [-4; 7; 14; 3; -6; 3; 0; -8; 6; 2; 0; 1; 8; -4; 7] 
  [-4; 7; 14; 0; -6; 3; 2; -8; 6; 3; 0; 1; 8; -4; 7].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* Check the first 15 indices explicitly *)
      do 15 (destruct i; [ 
        simpl; 
        try (exfalso; vm_compute in H; congruence); 
        reflexivity 
      | ]).
      (* For i >= 15, both lists are empty *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        apply Permutation_refl.
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat (match goal with
                | [ |- Sorted _ (_ :: _) ] => apply Sorted_cons
                | [ |- Sorted _ [] ] => apply Sorted_nil
                | [ |- HdRel _ (_ :: _) ] => apply HdRel_cons
                | [ |- HdRel _ [] ] => apply HdRel_nil
                | [ |- Z.le _ _ ] => compute; reflexivity
                end).
Qed.