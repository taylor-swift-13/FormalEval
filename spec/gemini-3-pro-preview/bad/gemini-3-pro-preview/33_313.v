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
  [900; 2; 7; 11; 9; 3; -7; 8; 0; 1; -12; 6; 200; -2; 19; 13] 
  [-7; 2; 7; 1; 9; 3; 11; 8; 0; 13; -12; 6; 200; -2; 19; 900].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* We destruct i 16 times to evaluate nth_error for all indices in range. *)
      (* For indices out of range, nth_error returns None for both. *)
      do 16 (destruct i; [ simpl in *; try congruence; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* Since elements are unique, we can use NoDup_Permutation *)
        apply NoDup_Permutation.
        -- (* NoDup l *)
           repeat (constructor; [ intro H_in; simpl in H_in; repeat destruct H_in; discriminate | ]).
           apply NoDup_nil.
        -- (* NoDup res *)
           repeat (constructor; [ intro H_in; simpl in H_in; repeat destruct H_in; discriminate | ]).
           apply NoDup_nil.
        -- (* In l <-> In res *)
           intros x. split; intro H_in; simpl in *;
           repeat (destruct H_in as [H_eq | H_in]; [ subst; simpl; auto | ]);
           contradiction.
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat apply Sorted_cons.
        -- apply Sorted_nil.
        -- apply HdRel_nil.
        -- constructor. cbv. discriminate.
        -- constructor. cbv. discriminate.
        -- constructor. cbv. discriminate.
        -- constructor. cbv. discriminate.
        -- constructor. cbv. discriminate.
Qed.