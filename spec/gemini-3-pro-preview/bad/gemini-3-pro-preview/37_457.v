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

Example test_sort_even_case : sort_even_spec [11; -7; 2; 10; 0; 5; -3; 2; 8; 3; 7] [-3; -7; 0; 10; 2; 5; 7; 2; 8; 3; 11].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      destruct i; [ simpl in Hodd; discriminate | ].
      destruct i; [ reflexivity | ].
      destruct i; [ simpl in Hodd; discriminate | ].
      destruct i; [ reflexivity | ].
      destruct i; [ simpl in Hodd; discriminate | ].
      destruct i; [ reflexivity | ].
      destruct i; [ simpl in Hodd; discriminate | ].
      destruct i; [ reflexivity | ].
      destruct i; [ simpl in Hodd; discriminate | ].
      destruct i; [ reflexivity | ].
      destruct i; [ simpl in Hodd; discriminate | ].
      simpl in Hlen. lia.
    + split.
      * simpl.
        apply Permutation_sym.
        transitivity (-3 :: [11; 2; 0; 8; 7]).
        -- apply Permutation_cons.
           transitivity (0 :: [11; 2; 8; 7]).
           ++ apply Permutation_cons.
              transitivity (2 :: [11; 8; 7]).
              ** apply Permutation_cons.
                 transitivity (7 :: [11; 8]).
                 --- apply Permutation_cons.
                     apply Permutation_swap.
                 --- apply Permutation_sym.
                     change [11; 8; 7] with ([11; 8] ++ 7 :: []).
                     apply Permutation_middle.
              ** apply Permutation_sym.
                 change [11; 2; 8; 7] with ([11] ++ 2 :: [8; 7]).
                 apply Permutation_middle.
           ++ apply Permutation_sym.
              change [11; 2; 0; 8; 7] with ([11; 2] ++ 0 :: [8; 7]).
              apply Permutation_middle.
        -- apply Permutation_sym.
           change [11; 2; 0; -3; 8; 7] with ([11; 2; 0] ++ -3 :: [8; 7]).
           apply Permutation_middle.
      * simpl.
        apply Sorted_cons. { apply HdRel_cons. lia. }
        apply Sorted_cons. { apply HdRel_cons. lia. }
        apply Sorted_cons. { apply HdRel_cons. lia. }
        apply Sorted_cons. { apply HdRel_cons. lia. }
        apply Sorted_cons. { apply HdRel_cons. lia. }
        apply Sorted_cons. { apply HdRel_nil. }
        apply Sorted_nil.
Qed.