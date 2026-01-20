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
  [11; 22; 33; 44; 55; 66; 77; 88; 88; 32; 99; 77; 77; 11; 77; 66] 
  [11; 22; 33; 32; 55; 66; 44; 88; 88; 66; 99; 77; 77; 11; 77; 77].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      repeat (destruct i; [ simpl in *; try (exfalso; compute in H; congruence); reflexivity | ]).
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        (* Target: [11; 32; 44; 66; 77; 77] *)
        (* Source: [11; 44; 77; 32; 77; 66] *)
        simpl.
        apply perm_skip. (* Match 11 *)
        apply Permutation_trans with (l' := 44 :: 32 :: 66 :: 77 :: 77 :: []).
        { apply perm_swap. }
        apply perm_skip. (* Match 44 *)
        apply Permutation_trans with (l' := 77 :: 32 :: 66 :: 77 :: []).
        { apply Permutation_trans with (l' := 32 :: 77 :: 66 :: 77 :: []).
          { apply perm_skip. apply perm_swap. }
          { apply perm_swap. }
        }
        apply perm_skip. (* Match 77 *)
        apply perm_skip. (* Match 32 *)
        apply perm_swap. (* Swap 66 and 77 *)
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        apply Sorted_cons.
        { apply Sorted_cons.
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
        }
        { apply HdRel_cons. compute. discriminate. }
Qed.