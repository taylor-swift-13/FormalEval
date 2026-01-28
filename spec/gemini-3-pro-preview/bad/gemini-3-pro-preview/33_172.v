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

Lemma perm_move : forall A (x : A) l1 l2, Permutation (l1 ++ x :: l2) (x :: l1 ++ l2).
Proof. intros. apply Permutation_sym. apply Permutation_middle. Qed.

Example test_case : sort_third_spec 
  [300; 500; 6; 7; 200; 7; 289; 20; -105; -277; 104; 200; 3; 4; 5; 700; 900; -200; -901; 800; 1000; 6] 
  [-901; 500; 6; -277; 200; 7; 3; 20; -105; 6; 104; 200; 7; 4; 5; 289; 900; -200; 300; 800; 1000; 700].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 22 (destruct i; [ simpl in *; try (compute in H; contradiction); reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        transitivity (-901 :: [300; 7; 289; -277; 3; 700; 6]).
        { change ([300; 7; 289; -277; 3; 700; -901; 6]) with ([300; 7; 289; -277; 3; 700] ++ -901 :: [6]). apply perm_move. }
        apply perm_skip.
        transitivity (-277 :: [300; 7; 289; 3; 700; 6]).
        { change ([300; 7; 289; -277; 3; 700; 6]) with ([300; 7; 289] ++ -277 :: [3; 700; 6]). apply perm_move. }
        apply perm_skip.
        transitivity (3 :: [300; 7; 289; 700; 6]).
        { change ([300; 7; 289; 3; 700; 6]) with ([300; 7; 289] ++ 3 :: [700; 6]). apply perm_move. }
        apply perm_skip.
        transitivity (6 :: [300; 7; 289; 700]).
        { change ([300; 7; 289; 700; 6]) with ([300; 7; 289; 700] ++ 6 :: []). apply perm_move. }
        apply perm_skip.
        transitivity (7 :: [300; 289; 700]).
        { change ([300; 7; 289; 700]) with ([300] ++ 7 :: [289; 700]). apply perm_move. }
        apply perm_skip.
        transitivity (289 :: [300; 700]).
        { change ([300; 289; 700]) with ([300] ++ 289 :: [700]). apply perm_move. }
        apply perm_skip.
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [ simpl; intros Hc; discriminate | ]).
        apply Sorted_nil.
Qed.