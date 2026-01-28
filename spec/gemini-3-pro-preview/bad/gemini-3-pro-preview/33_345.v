Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
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
  [300; 500; 6; 7; 8; 289; 20; -105; -277; 104; 200; 3; -1; 5; 700; 900; -901; 800; 1000; 6; 0; -277; 500]
  [-277; 500; 6; -1; 8; 289; 7; -105; -277; 20; 200; 3; 104; 5; 700; 300; -901; 800; 900; 6; 0; 1000; 500].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      do 23 (destruct i as [|i]; [ simpl in *; try lia; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* Goal: Permutation [-277; -1; 7; 20; 104; 300; 900; 1000] [300; 7; 20; 104; -1; 900; 1000; -277] *)
        apply Permutation_sym.
        change ([300; 7; 20; 104; -1; 900; 1000; -277]) with ([300; 7; 20; 104; -1; 900; 1000] ++ [-277]).
        apply Permutation_app_comm.
        simpl. apply Permutation_cons.
        
        (* Goal: Permutation [-1; 7; 20; 104; 300; 900; 1000] [300; 7; 20; 104; -1; 900; 1000] *)
        apply Permutation_sym.
        change ([300; 7; 20; 104; -1; 900; 1000]) with ([300; 7; 20; 104] ++ -1 :: [900; 1000]).
        apply Permutation_middle.
        simpl. apply Permutation_cons.
        
        (* Goal: Permutation [7; 20; 104; 300; 900; 1000] [300; 7; 20; 104; 900; 1000] *)
        apply Permutation_sym. apply Permutation_swap.
        simpl. apply Permutation_cons.
        
        (* Goal: Permutation [20; 104; 300; 900; 1000] [300; 20; 104; 900; 1000] *)
        apply Permutation_sym. apply Permutation_swap.
        simpl. apply Permutation_cons.
        
        (* Goal: Permutation [104; 300; 900; 1000] [300; 104; 900; 1000] *)
        apply Permutation_sym. apply Permutation_swap.
        simpl. apply Permutation_cons.
        
        apply Permutation_refl.
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat (constructor; simpl; try lia).
Qed.