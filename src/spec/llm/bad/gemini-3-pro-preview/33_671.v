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
  [300; 500; 6; 7; 8; 289; 20; -105; -277; 104; 200; 3; 4; 5; 700; 900; 5; -200; -104; -901; 800] 
  [-104; 500; 6; 4; 8; 289; 7; -105; -277; 20; 200; 3; 104; 5; 700; 300; 5; -200; 900; -901; 800].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 21 (destruct i as [|i]; [ vm_compute in H; try contradiction; vm_compute; reflexivity | ]).
      vm_compute. reflexivity.
    + split.
      * simpl.
        apply Permutation_trans with (l' := -104 :: [300; 7; 20; 104; 4; 900]).
        { apply perm_skip.
          apply Permutation_trans with (l' := 4 :: [300; 7; 20; 104; 900]).
          { apply perm_skip.
            apply Permutation_trans with (l' := 7 :: [300; 20; 104; 900]).
            { apply perm_skip.
              apply Permutation_trans with (l' := 20 :: [300; 104; 900]).
              { apply perm_skip.
                apply Permutation_trans with (l' := 104 :: [300; 900]).
                { apply perm_skip.
                  reflexivity.
                }
                { apply Permutation_middle. }
              }
              { apply Permutation_middle. }
            }
            { apply Permutation_middle. }
          }
          { apply Permutation_middle. }
        }
        { apply Permutation_app_comm. }
      * simpl.
        repeat (constructor; [ simpl; try lia | ]).
        apply Sorted_nil.
Qed.