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
  [500; 6; 7; 8; 289; 20; -105; -277; 104; 200; 3; 4; 5; 700; 900; -200; -901; 801; 1000; -277; 7] 
  [-200; 6; 7; -105; 289; 20; 5; -277; 104; 8; 3; 4; 200; 700; 900; 500; -901; 801; 1000; -277; 7].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 21 (destruct i; [ simpl in *; try congruence; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl. apply NoDup_Permutation.
        -- repeat (constructor; [ simpl; intro C; repeat destruct C; discriminate | ]). apply NoDup_nil.
        -- repeat (constructor; [ simpl; intro C; repeat destruct C; discriminate | ]). apply NoDup_nil.
        -- intros x. split; intro Hx; simpl in *; repeat destruct Hx; subst; simpl; tauto.
      * simpl.
        repeat (apply Sorted_cons; [ | try apply HdRel_nil; try (apply HdRel_cons; apply Z.leb_le; reflexivity) ]).
        apply Sorted_nil.
Qed.