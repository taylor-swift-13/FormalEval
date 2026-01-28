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
  [300; 500; 6; 7; 8; 289; 21; -6; -105; -277; 104; 200; 3; 4; 5; 700; 900; -200; -901; 800; 1000; 8]
  [-901; 500; 6; -277; 8; 289; 3; -6; -105; 7; 104; 200; 8; 4; 5; 21; 900; -200; 300; 800; 1000; 700].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      repeat (match goal with 
              | |- context [nth_error (_ :: _) _] => 
                  destruct i as [|i]; 
                  [ simpl in *; try reflexivity; try (exfalso; apply H; reflexivity) 
                  | simpl ] 
              end).
      simpl in *. reflexivity.
    + split.
      * simpl.
        transitivity (-901 :: [300; 7; 21; -277; 3; 700] ++ [8]).
        2: { apply Permutation_middle. }
        apply Permutation_cons.
        simpl.
        transitivity (-277 :: [300; 7; 21] ++ [3; 700; 8]).
        2: { apply Permutation_middle. }
        apply Permutation_cons.
        simpl.
        transitivity (3 :: [300; 7; 21] ++ [700; 8]).
        2: { apply Permutation_middle. }
        apply Permutation_cons.
        simpl.
        transitivity (7 :: [300] ++ [21; 700; 8]).
        2: { apply Permutation_middle. }
        apply Permutation_cons.
        simpl.
        transitivity (8 :: [300; 21; 700] ++ []).
        2: { rewrite app_nil_r. apply Permutation_middle. }
        apply Permutation_cons.
        simpl.
        transitivity (21 :: [300] ++ [700]).
        2: { apply Permutation_middle. }
        apply Permutation_cons.
        simpl.
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [| simpl; try apply HdRel_nil; try apply HdRel_cons; apply Zle_bool_imp_le; reflexivity]).
        apply Sorted_nil.
Qed.