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

Lemma perm_mid : forall {A} (x : A) l1 l2, Permutation (x :: l1 ++ l2) (l1 ++ x :: l2).
Proof.
  intros A x l1 l2. induction l1 as [|a l1 IH].
  - simpl. apply Permutation_refl.
  - simpl. apply Permutation_trans with (a :: x :: l1 ++ l2).
    + apply perm_swap.
    + apply perm_skip. apply IH.
Qed.

Example test_sort_even_case : sort_even_spec [5; 3; -5; 2; -3; 3; 9; 0; 123; 1; -10] [-10; 3; -5; 2; -3; 3; 5; 0; 9; 1; 123].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 11 (destruct i; [ try (simpl in Hodd; discriminate); try (simpl; reflexivity) | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        apply Permutation_trans with (5 :: [-10; -5; -3] ++ [9; 123]).
        { apply perm_skip.
          apply Permutation_trans with (-5 :: [-10] ++ [-3; 9; 123]).
          { apply perm_skip.
            apply Permutation_trans with (-3 :: [-10] ++ [9; 123]).
            { apply perm_skip.
              apply Permutation_trans with (9 :: [-10] ++ [123]).
              { apply perm_skip. apply perm_swap. }
              { apply perm_mid. }
            }
            { apply perm_mid. }
          }
          { apply perm_mid. }
        }
        { apply perm_mid. }
      * simpl.
        repeat (apply Sorted_cons; [| simpl; try lia]).
        apply Sorted_nil.
Qed.