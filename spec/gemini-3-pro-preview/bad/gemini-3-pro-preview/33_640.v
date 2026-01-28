Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Micromega.Lia.
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
  [300; 500; 6; 7; 289; 20; -105; 899; -277; 104; 8; 7; 3; 4; 5; 19; 700; 900; -200; -901; 800; 1000; 500] 
  [-200; 500; 6; -105; 289; 20; 3; 899; -277; 7; 8; 7; 19; 4; 5; 104; 700; 900; 300; -901; 800; 1000; 500].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* Check for each index i < 23 *)
      do 23 (destruct i as [|i]; [ 
        simpl in *; 
        try (contradict H; vm_compute; congruence);
        reflexivity 
      | ]).
      (* For i >= 23, both are None *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* We prove Permutation manually by moving elements to match the unsorted list *)
        (* Goal: Permutation [-200; -105; 3; 7; 19; 104; 300; 1000] [300; 7; -105; 104; 3; 19; -200; 1000] *)
        transitivity (-200 :: [300; 7; -105; 104; 3; 19] ++ [1000]).
        { apply Permutation_cons.
          transitivity (-105 :: [300; 7] ++ [104; 3; 19; 1000]).
          { apply Permutation_cons.
            transitivity (3 :: [300; 7; 104] ++ [19; 1000]).
            { apply Permutation_cons.
              transitivity (7 :: [300] ++ [104; 19; 1000]).
              { apply Permutation_cons.
                transitivity (19 :: [300; 104] ++ [1000]).
                { apply Permutation_cons.
                  transitivity (104 :: [300] ++ [1000]).
                  { apply Permutation_cons.
                    transitivity (300 :: [] ++ [1000]).
                    { apply Permutation_cons.
                      apply Permutation_refl. }
                    { apply Permutation_middle. } }
                  { apply Permutation_middle. } }
                { apply Permutation_middle. } }
              { apply Permutation_middle. } }
            { apply Permutation_middle. } }
          { apply Permutation_middle. } }
        { apply Permutation_middle. }
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat (apply Sorted_cons; [ | try (apply HdRel_cons; simpl; lia); try apply HdRel_nil ]).
        apply Sorted_nil.
Qed.