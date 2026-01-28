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
  [300; 500; 6; 289; 20; -105; -277; 104; 200; 3; 4; 5; 700; 5; -200; -104; -901; 800; 29; 5] 
  [-277; 500; 6; -104; 20; -105; 3; 104; 200; 29; 4; 5; 289; 5; -200; 300; -901; 800; 700; 5].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 20 (destruct i; [ simpl in *; try (exfalso; apply H; reflexivity); reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply (Permutation_trans _ (-277 :: [300; 289; 3; 700; -104; 29])).
        { apply Permutation_cons.
          apply (Permutation_trans _ (-104 :: [300; 289; 3; 700; 29])).
          { apply Permutation_cons.
            apply (Permutation_trans _ (3 :: [300; 289; 700; 29])).
            { apply Permutation_cons.
              apply (Permutation_trans _ (29 :: [300; 289; 700])).
              { apply Permutation_cons.
                apply (Permutation_trans _ (289 :: [300; 700])).
                { apply Permutation_cons.
                  apply Permutation_refl.
                }
                { apply Permutation_middle. }
              }
              { apply Permutation_middle. }
            }
            { apply Permutation_middle. }
          }
          { apply Permutation_middle. }
        }
        { apply Permutation_middle. }
      * simpl.
        repeat apply Sorted_cons.
        -- apply Sorted_nil.
        -- apply HdRel_nil.
        -- apply HdRel_cons; hnf; simpl; intro; discriminate.
        -- apply HdRel_cons; hnf; simpl; intro; discriminate.
        -- apply HdRel_cons; hnf; simpl; intro; discriminate.
        -- apply HdRel_cons; hnf; simpl; intro; discriminate.
        -- apply HdRel_cons; hnf; simpl; intro; discriminate.
        -- apply HdRel_cons; hnf; simpl; intro; discriminate.
Qed.