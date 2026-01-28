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
  [300; 6; 7; 290; 8; 289; 20; -105; -277; 104; 200; 3; 4; 700; 900; -902; 800; 1000; 103; 3]
  [-902; 6; 7; 4; 8; 289; 20; -105; -277; 103; 200; 3; 104; 700; 900; 290; 800; 1000; 300; 3].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* Destruct i enough times to cover the concrete list length (20) *)
      repeat (destruct i; [ simpl in *; try (exfalso; lia); reflexivity | ]).
      (* For i >= 20, both lists are empty *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* We prove permutation by manually moving elements to match the sorted order *)
        apply Permutation_sym.
        transitivity (300 :: [-902; 4; 20; 103; 104; 290]).
        { apply Permutation_cons.
          transitivity (290 :: [-902; 4; 20; 103; 104]).
          { apply Permutation_cons.
            transitivity (20 :: [-902; 4] ++ [103; 104]).
            { apply Permutation_cons.
              transitivity (104 :: [-902; 4; 103]).
              { apply Permutation_cons.
                transitivity (4 :: [-902] ++ [103]).
                { apply Permutation_cons.
                  apply Permutation_refl.
                  symmetry. apply Permutation_middle. }
                apply Permutation_cons_append. }
              symmetry. apply Permutation_middle. }
            apply Permutation_cons_append. }
          apply Permutation_cons_append. }
        apply Permutation_cons_append.
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        (* Prove Sorted by repeatedly applying constructors and checking HdRel with lia *)
        repeat (apply Sorted_cons; [ | simpl; try apply HdRel_nil; apply HdRel_cons; lia ]).
        apply Sorted_nil.
Qed.