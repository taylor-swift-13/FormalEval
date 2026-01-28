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
  [5; 2; 7; 9; 3; -6; -6; 288; 300; 1; 13; 6; -2; 19] 
  [-6; 2; 7; -2; 3; -6; 1; 288; 300; 5; 13; 6; 9; 19].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* We check for i = 0 to 14. For larger i, nth_error is None. *)
      do 15 (destruct i; [ 
        simpl in *; 
        try (exfalso; compute in H; congruence); 
        reflexivity 
      | ]).
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* Goal: Permutation [-6; -2; 1; 5; 9] [5; 9; -6; 1; -2] *)
        transitivity (-6 :: ([5; 9] ++ [1; -2])); [ apply Permutation_cons | apply Permutation_middle ].
        transitivity (-2 :: ([5; 9; 1] ++ [])); [ apply Permutation_cons | apply Permutation_middle ].
        transitivity (1 :: ([5; 9] ++ [])); [ apply Permutation_cons | apply Permutation_middle ].
        apply Permutation_refl.
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat (apply Sorted_cons; [ | first [ apply HdRel_nil | apply HdRel_cons; simpl; lia ] ]).
        apply Sorted_nil.
Qed.