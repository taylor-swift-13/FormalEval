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
  [301; 500; 6; 7; 290; 8; 289; 20; -105; -277; 104; 200; 3; 4; 700; 900; -901; 800; 1000; -901; 1000; 20]
  [-277; 500; 6; 3; 290; 8; 7; 20; -105; 20; 104; 200; 289; 4; 700; 301; -901; 800; 900; -901; 1000; 1000].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      (* Verify preservation for indices not divisible by 3 *)
      do 22 (destruct i; [ simpl; try reflexivity; try congruence | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        (* Prove Permutation by rearranging the list manually *)
        apply Permutation_sym.
        (* Move -277 to front *)
        change ([301; 7; 289; -277; 3; 900; 1000; 20]) with ([301; 7; 289] ++ -277 :: [3; 900; 1000; 20]).
        apply Permutation_trans with (l' := -277 :: [301; 7; 289] ++ [3; 900; 1000; 20]).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons. simpl.
        (* Move 3 to front *)
        change ([301; 7; 289; 3; 900; 1000; 20]) with ([301; 7; 289] ++ 3 :: [900; 1000; 20]).
        apply Permutation_trans with (l' := 3 :: [301; 7; 289] ++ [900; 1000; 20]).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons. simpl.
        (* Move 7 to front *)
        change ([301; 7; 289; 900; 1000; 20]) with ([301] ++ 7 :: [289; 900; 1000; 20]).
        apply Permutation_trans with (l' := 7 :: [301] ++ [289; 900; 1000; 20]).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons. simpl.
        (* Move 20 to front *)
        change ([301; 289; 900; 1000; 20]) with ([301; 289; 900; 1000] ++ 20 :: []).
        apply Permutation_trans with (l' := 20 :: [301; 289; 900; 1000] ++ []).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons. simpl.
        (* Move 289 to front *)
        change ([301; 289; 900; 1000]) with ([301] ++ 289 :: [900; 1000]).
        apply Permutation_trans with (l' := 289 :: [301] ++ [900; 1000]).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons. simpl.
        (* The rest is already sorted: 301, 900, 1000 *)
        apply Permutation_refl.
      * simpl.
        repeat constructor.
Qed.