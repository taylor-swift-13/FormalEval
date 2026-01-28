Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Micromega.Lra.
Require Import Coq.Micromega.Lia.
Import ListNotations.
Open Scope R_scope.

Fixpoint extract_thirds (l : list R) (i : nat) : list R :=
  match l with
  | [] => []
  | x :: xs => 
      if (i mod 3 =? 0)%nat 
      then x :: extract_thirds xs (S i) 
      else extract_thirds xs (S i)
  end.

Definition sort_third_spec (l : list R) (res : list R) : Prop :=
  length res = length l /\
  (forall i : nat, (i mod 3 <> 0)%nat -> nth_error res i = nth_error l i) /\
  Permutation (extract_thirds res 0) (extract_thirds l 0) /\
  Sorted Rle (extract_thirds res 0).

Example test_case : sort_third_spec 
  [-99.72274847671751%R; -83.09912721681734%R; 72.36056595235235%R; 72.36056595235235%R; 40.58689270655174%R; -93.33888003792336%R; 8.760174116134323%R; 120.16237056855249%R; 72.36056595235235%R]
  [-99.72274847671751%R; -83.09912721681734%R; 72.36056595235235%R; 8.760174116134323%R; 40.58689270655174%R; -93.33888003792336%R; 72.36056595235235%R; 120.16237056855249%R; 72.36056595235235%R].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* Destruct i 9 times to handle all indices 0..8, then handle out of bounds *)
      do 9 (destruct i as [|i]; [ simpl in *; try reflexivity; try (exfalso; lia) | ]).
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* List is [-99.72; 8.76; 72.36] vs [-99.72; 72.36; 8.76] *)
        apply perm_skip.
        apply perm_swap.
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        (* List is [-99.72; 8.76; 72.36] *)
        apply Sorted_cons.
        -- apply Sorted_cons.
           ++ apply Sorted_cons.
              ** apply Sorted_nil.
              ** apply HdRel_nil.
           ++ apply HdRel_cons. lra.
        -- apply HdRel_cons. lra.
Qed.