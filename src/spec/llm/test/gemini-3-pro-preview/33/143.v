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
  [-4; 7; 3; -6; 1000; 0; -8; 6; 2; 289; 1] 
  [-8; 7; 3; -6; 1000; 0; -4; 6; 2; 289; 1].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* Break down the indices to handle concrete values *)
      do 11 (destruct i; [ simpl in H; try contradiction; simpl; reflexivity | ]).
      (* For i >= 11 *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* Goal: Permutation [-8; -6; -4; 289] [-4; -6; -8; 289] *)
        apply perm_trans with (l' := [-8; -4; -6; 289]).
        -- apply perm_skip. apply perm_swap.
        -- apply perm_trans with (l' := [-4; -8; -6; 289]).
           ++ apply perm_swap.
           ++ apply perm_skip. apply perm_swap.
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        apply Sorted_cons.
        { apply Sorted_cons.
          { apply Sorted_cons.
            { apply Sorted_cons.
              { apply Sorted_nil. }
              { apply HdRel_nil. }
            }
            { apply HdRel_cons. compute. discriminate. }
          }
          { apply HdRel_cons. compute. discriminate. }
        }
        { apply HdRel_cons. compute. discriminate. }
Qed.