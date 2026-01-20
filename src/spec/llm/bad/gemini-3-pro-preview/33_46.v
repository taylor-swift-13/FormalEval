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

Example test_case : sort_third_spec [2; 4; 20; 15; 18; 13; 7] [2; 4; 20; 7; 18; 13; 15].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* We check i = 0..6 explicitly, and i >= 7 *)
      repeat (destruct i as [|i]; [
        (* Check specific index *)
        simpl in H; try discriminate; simpl; reflexivity
      | ]).
      (* For i >= 7, both lists are empty/None *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        (* [2; 7; 15] vs [2; 15; 7] *)
        simpl.
        apply perm_skip.
        apply perm_swap.
      * (* 4. Sortedness of extracted thirds *)
        (* [2; 7; 15] *)
        simpl.
        apply Sorted_cons.
        { apply Sorted_cons.
          { apply Sorted_cons.
            { apply Sorted_nil. }
            { apply HdRel_nil. } }
          { apply HdRel_cons. unfold Z.le. simpl. intro. discriminate. } }
        { apply HdRel_cons. unfold Z.le. simpl. intro. discriminate. }
Qed.