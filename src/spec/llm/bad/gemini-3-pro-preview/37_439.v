Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope Z_scope.

Fixpoint get_evens (l : list Z) : list Z :=
  match l with
  | [] => []
  | x :: [] => [x]
  | x :: _ :: tl => x :: get_evens tl
  end.

Definition sort_even_spec (l res : list Z) : Prop :=
  length l = length res /\
  (forall i : nat, (i < length l)%nat -> Nat.odd i = true -> nth i l 0 = nth i res 0) /\
  Permutation (get_evens l) (get_evens res) /\
  Sorted Z.le (get_evens res).

Example test_sort_even_case : sort_even_spec 
  [5; -13; 3; -5; 2; -3; -2; 3; -8; 0; 1; -10; -9] 
  [-9; -13; -8; -5; -2; -3; 1; 3; 2; 0; 3; -10; 5].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      do 13 (destruct i as [|i]; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        apply Permutation_trans with (5 :: [-9; -8; -2; 1; 2; 3]).
        { apply perm_skip.
          apply Permutation_trans with (3 :: [-9; -8; -2; 1; 2]).
          { apply perm_skip.
            apply Permutation_trans with (2 :: [-9; -8; -2; 1]).
            { apply perm_skip.
              apply Permutation_trans with (-2 :: [-9; -8; 1]).
              { apply perm_skip.
                apply Permutation_trans with (-8 :: [-9; 1]).
                { apply perm_skip.
                  apply Permutation_trans with (1 :: [-9]).
                  { apply perm_skip. apply Permutation_refl. }
                  { apply Permutation_middle. }
                }
                { apply Permutation_middle. }
              }
              { apply Permutation_middle. }
            }
            { apply Permutation_cons_append. }
          }
          { apply Permutation_cons_append. }
        }
        { apply Permutation_cons_append. }
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [ | apply HdRel_cons; lia ]).
        apply Sorted_nil.
Qed.