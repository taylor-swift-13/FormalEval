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
  [-4; 8; 3; -6; 3; 0; -8; 6; 799; 2; 1; 800; 0; 800] 
  [-8; 8; 3; -6; 3; 0; -4; 6; 799; 0; 1; 800; 2; 800].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* Since the list is finite (length 14), we can destruct i 14 times.
         This prevents timeouts from symbolic evaluation of nth_error/mod. *)
      do 14 (destruct i; [ 
        simpl in *; 
        try (elim H; reflexivity); (* If i mod 3 = 0, H is false *)
        reflexivity (* If i mod 3 <> 0, check equality *)
      | ]).
      (* For i >= 14, both nth_error are None *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* Goal: Permutation [-8; -6; -4; 0; 2] [-4; -6; -8; 2; 0] *)
        apply Permutation_cons_app with (l1:=[-4; -6]) (l2:=[2; 0]). simpl.
        apply Permutation_cons_app with (l1:=[-4]) (l2:=[2; 0]). simpl.
        apply Permutation_cons_app with (l1:=[]) (l2:=[2; 0]). simpl.
        apply Permutation_cons_app with (l1:=[2]) (l2:=[]). simpl.
        apply Permutation_refl.
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat (apply Sorted_cons; [ | apply HdRel_nil || (apply HdRel_cons; compute; congruence) ]).
        apply Sorted_nil.
Qed.