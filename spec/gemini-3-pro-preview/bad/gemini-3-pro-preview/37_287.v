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

Example test_sort_even_case : sort_even_spec 
  [0; 3; -5; 2; -3; -3; 3; -9; 123; 1; -10] 
  [-10; 3; -5; 2; -3; -3; 0; -9; 3; 1; 123].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      destruct i. { simpl in Hodd. discriminate. }
      destruct i. { simpl. reflexivity. }
      destruct i. { simpl in Hodd. discriminate. }
      destruct i. { simpl. reflexivity. }
      destruct i. { simpl in Hodd. discriminate. }
      destruct i. { simpl. reflexivity. }
      destruct i. { simpl in Hodd. discriminate. }
      destruct i. { simpl. reflexivity. }
      destruct i. { simpl in Hodd. discriminate. }
      destruct i. { simpl. reflexivity. }
      destruct i. { simpl in Hodd. discriminate. }
      (* i >= 11 *)
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Input evens: [0; -5; -3; 3; 123; -10] *)
        (* Target evens: [-10; -5; -3; 0; 3; 123] *)
        
        transitivity (-10 :: [0; -5; -3; 3; 123]).
        { apply Permutation_sym.
          replace [0; -5; -3; 3; 123; -10] with ([0; -5; -3; 3; 123] ++ [-10]) by (simpl; reflexivity).
          apply Permutation_middle. }
        apply Permutation_cons.
        
        transitivity (-5 :: [0; -3; 3; 123]).
        { apply Permutation_sym.
          replace [0; -5; -3; 3; 123] with ([0] ++ [-5] ++ [-3; 3; 123]) by (simpl; reflexivity).
          apply Permutation_middle. }
        apply Permutation_cons.
        
        transitivity (-3 :: [0; 3; 123]).
        { apply Permutation_sym.
          replace [0; -3; 3; 123] with ([0] ++ [-3] ++ [3; 123]) by (simpl; reflexivity).
          apply Permutation_middle. }
        apply Permutation_cons.
        
        apply Permutation_refl.
        
      * (* 4. Sorted check *)
        simpl.
        apply Sorted_cons.
        { apply Sorted_cons.
          { apply Sorted_cons.
            { apply Sorted_cons.
              { apply Sorted_cons.
                { apply Sorted_cons.
                  { apply Sorted_nil. }
                  { apply HdRel_nil. } }
                { apply HdRel_cons. lia. } }
              { apply HdRel_cons. lia. } }
            { apply HdRel_cons. lia. } }
          { apply HdRel_cons. lia. } }
        { apply HdRel_cons. lia. }
Qed.