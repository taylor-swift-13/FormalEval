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

Lemma perm_mid : forall A (x : A) l1 l2, Permutation (l1 ++ x :: l2) (x :: l1 ++ l2).
Proof.
  intros. induction l1.
  - simpl. apply Permutation_refl.
  - simpl. eapply perm_trans.
    2: apply perm_swap.
    apply perm_skip. apply IHl1.
Qed.

Example test_case : sort_third_spec 
  [300; 500; 6; 7; 8; 289; 20; -105; -277; 104; 8; 7; 3; 12; 4; 5; 700; 900; -200; -901; 800; 1000]
  [-200; 500; 6; 3; 8; 289; 5; -105; -277; 7; 8; 7; 20; 12; 4; 104; 700; 900; 300; -901; 800; 1000].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 22 (destruct i; [ simpl; try reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        change ([300; 7; 20; 104; 3; 5; -200; 1000]) with ([300; 7; 20; 104; 3; 5] ++ -200 :: [1000]).
        apply perm_mid.
        apply perm_skip.
        change ([300; 7; 20; 104; 3; 5; 1000]) with ([300; 7; 20; 104] ++ 3 :: [5; 1000]).
        apply perm_mid.
        apply perm_skip.
        change ([300; 7; 20; 104; 5; 1000]) with ([300; 7; 20; 104] ++ 5 :: [1000]).
        apply perm_mid.
        apply perm_skip.
        change ([300; 7; 20; 104; 1000]) with ([300] ++ 7 :: [20; 104; 1000]).
        apply perm_mid.
        apply perm_skip.
        change ([300; 20; 104; 1000]) with ([300] ++ 20 :: [104; 1000]).
        apply perm_mid.
        apply perm_skip.
        change ([300; 104; 1000]) with ([300] ++ 104 :: [1000]).
        apply perm_mid.
        apply perm_skip.
        apply Permutation_refl.
      * simpl. repeat constructor.
Qed.