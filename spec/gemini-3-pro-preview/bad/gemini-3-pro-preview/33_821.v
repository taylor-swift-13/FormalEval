Existing Coq output file content 
specification for the test case `input = [[300%Z; 500%Z; 6%Z; 7%Z; 8%Z; 289%Z; 20%Z; -105%Z; 104%Z; -199%Z; 200%Z; 3%Z; 4%Z; 5%Z; 700%Z; 900%Z; 699%Z; -200%Z; -901%Z; 800%Z; 1000%Z]], output = [-901%Z; 500%Z; 6%Z; -199%Z; 8%Z; 289%Z; 4%Z; -105%Z; 104%Z; 7%Z; 200%Z; 3%Z; 20%Z; 5%Z; 700%Z; 300%Z; 699%Z; -200%Z; 900%Z; 800%Z; 1000%Z]`:
```coq
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
  [300; 500; 6; 7; 8; 289; 20; -105; 104; -199; 200; 3; 4; 5; 700; 900; 699; -200; -901; 800; 1000]
  [-901; 500; 6; -199; 8; 289; 4; -105; 104; 7; 200; 3; 20; 5; 700; 300; 699; -200; 900; 800; 1000].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 25 (destruct i; [ simpl in H; try (exfalso; congruence); simpl; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply (Permutation_trans (l' := -901 :: [300; 7; 20; -199; 4; 900])).
        2: { change [300; 7; 20; -199; 4; 900; -901] with ([300; 7; 20; -199; 4; 900] ++ [-901]).
             apply Permutation_middle. }
        apply perm_skip.
        
        apply (Permutation_trans (l' := -199 :: [300; 7; 20; 4; 900])).
        2: { change [300; 7; 20; -199; 4; 900] with ([300; 7; 20] ++ -199 :: [4; 900]).
             apply Permutation_middle. }
        apply perm_skip.
        
        apply (Permutation_trans (l' := 4 :: [300; 7; 20; 900])).
        2: { change [300; 7; 20; 4; 900] with ([300; 7; 20] ++ 4 :: [900]).
             apply Permutation_middle. }
        apply perm_skip.
        
        apply (Permutation_trans (l' := 7 :: [300; 20; 900])).
        2: { change [300; 7; 20; 900] with ([300] ++ 7 :: [20; 900]).
             apply Permutation_middle. }
        apply perm_skip.
        
        apply (Permutation_trans (l' := 20 :: [300; 900])).
        2: { change [300; 20; 900] with ([300] ++ 20 :: [900]).
             apply Permutation_middle. }
        apply perm_skip.
        
        apply Permutation_refl.
      * simpl. repeat (constructor; try (vm_compute; discriminate)).
Qed.