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
  [500; 6; 7; 8; 289; 20; -105; -277; 104; 200; 3; 4; 5; 700; 900; -200; -901; 800; 1000; -277]
  [-200; 6; 7; -105; 289; 20; 5; -277; 104; 8; 3; 4; 200; 700; 900; 500; -901; 800; 1000; -277].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      destruct (le_lt_dec 20 i).
      * rewrite !nth_error_None; simpl; lia.
      * do 20 (destruct i as [|i]; [
          simpl; try (exfalso; apply H; reflexivity); reflexivity
        | ]).
        lia.
    + split.
      * simpl.
        apply (Permutation_trans (l' := -200 :: [500; 8; -105; 200; 5; 1000])).
        { apply perm_skip.
          apply (Permutation_trans (l' := -105 :: [500; 8; 200; 5; 1000])).
          { apply perm_skip.
            apply (Permutation_trans (l' := 5 :: [500; 8; 200; 1000])).
            { apply perm_skip.
              apply (Permutation_trans (l' := 8 :: [500; 200; 1000])).
              { apply perm_skip.
                apply (Permutation_trans (l' := 200 :: [500; 1000])).
                { apply perm_skip.
                  apply Permutation_refl.
                }
                change [500; 200; 1000] with ([500] ++ 200 :: [1000]).
                apply Permutation_sym; apply Permutation_middle.
              }
              change [500; 8; 200; 1000] with ([500] ++ 8 :: [200; 1000]).
              apply Permutation_sym; apply Permutation_middle.
            }
            change [500; 8; 200; 5; 1000] with ([500; 8; 200] ++ 5 :: [1000]).
            apply Permutation_sym; apply Permutation_middle.
          }
          change [500; 8; -105; 200; 5; 1000] with ([500; 8] ++ -105 :: [200; 5; 1000]).
          apply Permutation_sym; apply Permutation_middle.
        }
        change [500; 8; -105; 200; 5; -200; 1000] with ([500; 8; -105; 200; 5] ++ -200 :: [1000]).
        apply Permutation_sym; apply Permutation_middle.
      * simpl.
        repeat (apply Sorted_cons || apply Sorted_nil || (apply HdRel_cons; simpl; lia) || apply HdRel_nil).
Qed.