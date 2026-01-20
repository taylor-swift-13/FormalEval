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
  [300; 500; 6; 7; 291; 8; -3; 289; 20; 104; -277; 8; 200; -8; 700; 900; -901; 800; 1000; 290; -8; 200]
  [-3; 500; 6; 7; 291; 8; 104; 289; 20; 200; -277; 8; 200; -8; 700; 300; -901; 800; 900; 290; -8; 1000].
Proof.
  unfold sort_third_spec.
  split.
  - (* length *) 
    simpl. reflexivity.
  - split.
    + (* indices *)
      intros i H.
      (* Iterate destruct i to handle each index up to the list length (22) *)
      do 22 (destruct i; [ simpl in *; try (intros C; discriminate C); reflexivity | ]).
      (* Handle i >= 22 *)
      simpl. reflexivity.
    + split.
      * (* Permutation *)
        simpl.
        (* We prove permutation by moving elements one by one to match the sorted order *)
        
        (* 1. Move -3 to front *)
        transitivity (-3 :: 300 :: 7 :: 104 :: 200 :: 900 :: 1000 :: 200 :: []).
        2: { apply Permutation_middle. }
        apply Permutation_cons.

        (* 2. Move 7 to front *)
        transitivity (7 :: 300 :: 104 :: 200 :: 900 :: 1000 :: 200 :: []).
        2: { constructor. } (* swap 300 and 7 *)
        apply Permutation_cons.

        (* 3. Move 104 to front *)
        transitivity (104 :: 300 :: 200 :: 900 :: 1000 :: 200 :: []).
        2: { constructor. } (* swap 300 and 104 *)
        apply Permutation_cons.

        (* 4. Move 200 to front *)
        transitivity (200 :: 300 :: 900 :: 1000 :: 200 :: []).
        2: { constructor. } (* swap 300 and 200 *)
        apply Permutation_cons.

        (* 5. Move the other 200 to front *)
        transitivity (200 :: 300 :: 900 :: 1000 :: []).
        2: { apply Permutation_middle. }
        apply Permutation_cons.

        (* Remaining list [300; 900; 1000] matches *)
        apply Permutation_refl.

      * (* Sorted *)
        simpl.
        (* Verify sortedness by checking Z.le for each adjacent pair *)
        repeat (constructor; [ unfold Z.le; simpl; discriminate | ]).
        apply Sorted_nil.
Qed.