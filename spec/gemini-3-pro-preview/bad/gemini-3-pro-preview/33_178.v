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
  [900; 2; 7; 11; 9; 3; -7; 11; 8; 0; 1; 13; 6; -2; 19] 
  [-7; 2; 7; 0; 9; 3; 6; 11; 8; 11; 1; 13; 900; -2; 19].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* We destruct i 15 times to cover the list length *)
      do 15 (destruct i; [ 
        simpl in H; 
        try (exfalso; compute in H; congruence); 
        simpl; reflexivity 
      | ]).
      (* Out of bounds case *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* Use NoDup_Permutation to prove permutation of concrete lists *)
        apply NoDup_Permutation.
        -- repeat (constructor; [intro Hin; simpl in Hin; tauto | ]). apply NoDup_nil.
        -- repeat (constructor; [intro Hin; simpl in Hin; tauto | ]). apply NoDup_nil.
        -- intro x. simpl. tauto.
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        (* Prove sortedness by construction *)
        repeat (apply Sorted_cons; [ | simpl; first [ apply HdRel_nil | apply HdRel_cons; cbv; intro Hc; discriminate ] ]).
        apply Sorted_nil.
Qed.