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
  [300; 500; 6; 7; 290; 8; 289; 20; 104; -277; 8; 104; 200; -8; 700; 900; -901; 800; 1000; 290; -8] 
  [-277; 500; 6; 7; 290; 8; 200; 20; 104; 289; 8; 104; 300; -8; 700; 900; -901; 800; 1000; 290; -8].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 21 (destruct i; [ simpl; try reflexivity; simpl in H; try discriminate | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        transitivity (-277 :: [300; 7; 289] ++ [200; 900; 1000]).
        { apply Permutation_cons. 
          transitivity (7 :: 300 :: [289; 200; 900; 1000]).
          { apply Permutation_cons.
            transitivity (200 :: [300; 289] ++ [900; 1000]).
            { apply Permutation_cons.
              transitivity (289 :: 300 :: [900; 1000]).
              { apply Permutation_cons. apply Permutation_refl. }
              { apply Permutation_swap. }
            }
            { apply Permutation_middle with (l1 := [300; 289]). }
          }
          { apply Permutation_swap. }
        }
        { apply Permutation_middle with (l1 := [300; 7; 289]). }
      * simpl.
        repeat (apply Sorted_cons; [| simpl; try apply HdRel_nil; try (apply HdRel_cons; apply Z.leb_le; vm_compute; reflexivity) ]).
        apply Sorted_nil.
Qed.