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

Example test_case : sort_third_spec [500; 6; 7; -2; 8; 289; 20; -105; -277; 104; 200; 3; 4; 5; 11; 700; -200; -901; 800; 1000; -277; 289] [-2; 6; 7; 4; 8; 289; 20; -105; -277; 104; 200; 3; 289; 5; 11; 500; -200; -901; 700; 1000; -277; 800].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 23 (destruct i as [|i]; [ simpl; try reflexivity; try (exfalso; apply H; reflexivity) | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply Permutation_trans with (l' := -2 :: [500; 20; 104; 4; 700; 800; 289]).
        { apply perm_skip.
          apply Permutation_trans with (l' := 4 :: [500; 20; 104; 700; 800; 289]).
          { apply perm_skip.
            apply Permutation_trans with (l' := 20 :: [500; 104; 700; 800; 289]).
            { apply perm_skip.
              apply Permutation_trans with (l' := 104 :: [500; 700; 800; 289]).
              { apply perm_skip.
                apply Permutation_trans with (l' := 289 :: [500; 700; 800]).
                { apply perm_skip.
                  apply Permutation_refl. }
                { apply Permutation_middle. } }
              { apply Permutation_middle. } }
            { apply Permutation_middle. } }
          { apply Permutation_middle. } }
        { apply Permutation_middle. }
      * simpl.
        repeat (apply Sorted_cons; [ | unfold Z.le; simpl; try (intro H; discriminate) ]).
        apply Sorted_nil.
Qed.