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
  [500; 9; 8; 7; 6; 5; 4; 2; 1; -7; -1; -2; -3; -4; -1; -5; -6; -7; -8; -9; -11] 
  [-8; 9; 8; -7; 6; 5; -5; 2; 1; -3; -1; -2; 4; -4; -1; 7; -6; -7; 500; -9; -11].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      do 21 (destruct i as [|i]; [
        simpl in *;
        try (exfalso; vm_compute in H; contradiction);
        reflexivity
      | ]).
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        apply Permutation_trans with (l' := -8 :: [500; 7; 4; -7; -3; -5]).
        { apply Permutation_cons.
          apply Permutation_trans with (l' := -7 :: [500; 7; 4; -3; -5]).
          { apply Permutation_cons.
            apply Permutation_trans with (l' := -5 :: [500; 7; 4; -3]).
            { apply Permutation_cons.
              apply Permutation_trans with (l' := -3 :: [500; 7; 4]).
              { apply Permutation_cons.
                apply Permutation_trans with (l' := 4 :: [500; 7]).
                { apply Permutation_cons.
                  apply Permutation_trans with (l' := 7 :: [500]).
                  { apply Permutation_cons. apply Permutation_refl. }
                  apply Permutation_sym. apply (Permutation_middle 7 [500] []).
                }
                apply Permutation_sym. apply (Permutation_middle 4 [500; 7] []).
              }
              apply Permutation_sym. apply (Permutation_middle (-3) [500; 7; 4] []).
            }
            apply Permutation_sym. apply (Permutation_middle (-5) [500; 7; 4; -3] []).
          }
          apply Permutation_sym. apply (Permutation_middle (-7) [500; 7; 4] [-3; -5]).
        }
        apply Permutation_sym. apply (Permutation_middle (-8) [500; 7; 4; -7; -3; -5] []).
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat (apply Sorted_cons; [ simpl; cbv; intro Hc; discriminate | ]).
        apply Sorted_nil.
Qed.