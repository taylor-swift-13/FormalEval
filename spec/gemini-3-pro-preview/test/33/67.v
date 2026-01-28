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
  [46; 32; 77; 22; 18; 57; 57; 88; 66; 54] 
  [22; 32; 77; 46; 18; 57; 54; 88; 66; 57].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* Check indices 0 to 10 explicitly *)
      do 11 (destruct i; [ 
        simpl in H; try (elim H; reflexivity); simpl; reflexivity 
      | ]).
      (* For i >= 11, both lists are empty *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* Goal: Permutation [22; 46; 54; 57] [46; 22; 57; 54] *)
        apply Permutation_sym.
        transitivity ([22; 46; 57; 54]).
        { apply perm_swap. }
        { apply perm_skip. apply perm_skip. apply perm_swap. }
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        (* List: [22; 46; 54; 57] *)
        apply Sorted_cons.
        { apply Sorted_cons.
          { apply Sorted_cons.
            { apply Sorted_cons.
              { apply Sorted_nil. }
              { apply HdRel_nil. } }
            { apply HdRel_cons. vm_compute. discriminate. } }
          { apply HdRel_cons. vm_compute. discriminate. } }
        { apply HdRel_cons. vm_compute. discriminate. }
Qed.