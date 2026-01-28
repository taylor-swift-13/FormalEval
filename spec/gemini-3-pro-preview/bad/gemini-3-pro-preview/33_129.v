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
  [-4; 7; 3; -6; 3; 0; -8; 6; 2; 1; 8; 14; 0] 
  [-8; 7; 3; -6; 3; 0; -4; 6; 2; 0; 8; 14; 1].
Proof.
  unfold sort_third_spec.
  split.
  - (* length *)
    simpl. reflexivity.
  - split.
    + (* indices *)
      intros i H.
      do 13 (destruct i; [ simpl in *; try congruence; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * (* Permutation *)
        simpl.
        (* Goal: Permutation [-8; -6; -4; 0; 1] [-4; -6; -8; 1; 0] *)
        apply Permutation_trans with (l' := -8 :: [-4; -6; 1; 0]).
        { apply Permutation_cons.
          (* Goal: Permutation [-6; -4; 0; 1] [-4; -6; 1; 0] *)
          apply Permutation_trans with (l' := -6 :: [-4; 1; 0]).
          - apply Permutation_cons.
            (* Goal: Permutation [-4; 0; 1] [-4; 1; 0] *)
            apply Permutation_cons.
            apply Permutation_swap.
          - apply Permutation_sym.
            change (-4 :: -6 :: 1 :: 0 :: nil) with ((-4 :: nil) ++ -6 :: (1 :: 0 :: nil)).
            apply Permutation_middle.
        }
        { apply Permutation_sym.
          change (-4 :: -6 :: -8 :: 1 :: 0 :: nil) with ((-4 :: -6 :: nil) ++ -8 :: (1 :: 0 :: nil)).
          apply Permutation_middle.
        }
      * (* Sorted *)
        simpl.
        repeat (apply Sorted_cons; [ | first [ apply HdRel_nil | apply HdRel_cons; simpl; lia ] ]).
        apply Sorted_nil.
Qed.