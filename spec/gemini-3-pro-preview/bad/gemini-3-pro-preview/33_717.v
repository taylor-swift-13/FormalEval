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
  [300; 500; 6; 7; 290; 8; 289; 20; -105; -277; 104; -4; 3; 4; 700; 900; -901; 800; 1000; -901]
  [-277; 500; 6; 3; 290; 8; 7; 20; -105; 289; 104; -4; 300; 4; 700; 900; -901; 800; 1000; -901].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 21 (destruct i; [
        simpl in *;
        try (exfalso; vm_compute in H; congruence);
        reflexivity
      | ]).
      simpl. reflexivity.
    + split.
      * vm_compute.
        transitivity (-277 :: [300; 7; 289; 3; 700; 1000]).
        { apply Permutation_cons.
          transitivity (3 :: [300; 7; 289; 700; 1000]).
          { apply Permutation_cons.
            transitivity (7 :: [300; 289; 700; 1000]).
            { apply Permutation_cons.
              transitivity (289 :: [300; 700; 1000]).
              { apply Permutation_cons.
                apply Permutation_refl. }
              { change [300; 289; 700; 1000] with ([300] ++ 289 :: [700; 1000]).
                apply Permutation_middle. }
            }
            { change [300; 7; 289; 700; 1000] with ([300] ++ 7 :: [289; 700; 1000]).
              apply Permutation_middle. }
          }
          { change [300; 7; 289; 3; 700; 1000] with ([300; 7; 289] ++ 3 :: [700; 1000]).
            apply Permutation_middle. }
        }
        { change [300; 7; 289; -277; 3; 700; 1000] with ([300; 7; 289] ++ -277 :: [3; 700; 1000]).
          apply Permutation_middle. }
      * vm_compute.
        repeat (apply Sorted_cons; [ try apply HdRel_nil; try (apply HdRel_cons; lia) | ]).
        apply Sorted_nil.
Qed.