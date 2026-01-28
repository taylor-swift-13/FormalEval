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
  [300; 500; 6; 7; 290; 8; 289; 20; -105; -277; 104; 200; 3; 4; 700; -901; 0; 1000; 104]
  [-901; 500; 6; -277; 290; 8; 3; 20; -105; 7; 104; 200; 104; 4; 700; 289; 0; 1000; 300].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      do 19 (destruct i; [ simpl; try reflexivity; try (exfalso; apply H; auto; fail) | ]).
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        vm_compute.
        (* Goal: Permutation [-901; -277; 3; 7; 104; 289; 300] [300; 7; 289; -277; 3; -901; 104] *)
        
        (* Move -901 *)
        change [300; 7; 289; -277; 3; -901; 104] with ([300; 7; 289; -277; 3] ++ -901 :: [104]).
        apply Permutation_trans with (l' := -901 :: [300; 7; 289; -277; 3] ++ [104]).
        { apply Permutation_cons_app. }
        apply Permutation_cons.
        simpl.
        
        (* Move -277 *)
        change [300; 7; 289; -277; 3; 104] with ([300; 7; 289] ++ -277 :: [3; 104]).
        apply Permutation_trans with (l' := -277 :: [300; 7; 289] ++ [3; 104]).
        { apply Permutation_cons_app. }
        apply Permutation_cons.
        simpl.

        (* Move 3 *)
        change [300; 7; 289; 3; 104] with ([300; 7; 289] ++ 3 :: [104]).
        apply Permutation_trans with (l' := 3 :: [300; 7; 289] ++ [104]).
        { apply Permutation_cons_app. }
        apply Permutation_cons.
        simpl.

        (* Move 7 *)
        change [300; 7; 289; 104] with ([300] ++ 7 :: [289; 104]).
        apply Permutation_trans with (l' := 7 :: [300] ++ [289; 104]).
        { apply Permutation_cons_app. }
        apply Permutation_cons.
        simpl.

        (* Move 104 *)
        change [300; 289; 104] with ([300; 289] ++ 104 :: []).
        apply Permutation_trans with (l' := 104 :: [300; 289] ++ []).
        { apply Permutation_cons_app. }
        apply Permutation_cons.
        simpl.

        (* Move 289 *)
        change [300; 289] with ([300] ++ 289 :: []).
        apply Permutation_trans with (l' := 289 :: [300] ++ []).
        { apply Permutation_cons_app. }
        apply Permutation_cons.
        simpl.
        
        apply Permutation_refl.

      * (* 4. Sortedness of extracted thirds *)
        vm_compute.
        repeat apply Sorted_cons.
        -- apply Sorted_nil.
        -- all: simpl; try apply HdRel_nil; try (apply HdRel_cons; lia).
Qed.