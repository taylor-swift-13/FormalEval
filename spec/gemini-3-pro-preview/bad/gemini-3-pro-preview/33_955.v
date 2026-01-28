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
  [500; 6; 7; 8; 288; 20; -105; -277; 104; 200; 4; 3; 4; 5; 700; 900; -200; -901; 801; 1000; -277; 7] 
  [-105; 6; 7; 4; 288; 20; 7; -277; 104; 8; 4; 3; 200; 5; 700; 500; -200; -901; 801; 1000; -277; 900].
Proof.
  unfold sort_third_spec.
  split.
  - (* length *)
    simpl. reflexivity.
  - split.
    + (* indices *)
      intros i H.
      do 22 (destruct i; [ simpl in H; try contradiction; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * (* Permutation *)
        simpl.
        apply perm_trans with (-105 :: [500; 8; 200; 4; 900; 801; 7]).
        { apply perm_skip.
          apply perm_trans with (4 :: [500; 8; 200; 900; 801; 7]).
          { apply perm_skip.
            apply perm_trans with (7 :: [500; 8; 200; 900; 801]).
            { apply perm_skip.
              apply perm_trans with (8 :: [500; 200; 900; 801]).
              { apply perm_skip.
                apply perm_trans with (200 :: [500; 900; 801]).
                { apply perm_skip.
                  apply perm_trans with (500 :: [900; 801]).
                  { apply perm_skip.
                    apply perm_trans with (801 :: [900]).
                    { apply perm_skip.
                      apply perm_trans with (900 :: []).
                      { apply perm_skip. apply Permutation_refl. }
                      { apply Permutation_middle. }
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
          }
          { apply Permutation_middle. }
        }
        { apply Permutation_middle. }
      * (* Sorted *)
        simpl.
        repeat (apply Sorted_cons; [ | simpl; try apply HdRel_nil; try (apply Zle_bool_imp_le; reflexivity) ]).
        apply Sorted_nil.
Qed.