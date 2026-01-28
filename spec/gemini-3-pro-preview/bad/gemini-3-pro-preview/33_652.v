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
  [500; 6; 7; -2; 8; 289; 20; -105; -277; 104; 200; 3; 4; 5; 10; 700; 900; -200; -901; 800; 1000; -277]
  [-901; 6; 7; -277; 8; 289; -2; -105; -277; 4; 200; 3; 20; 5; 10; 104; 900; -200; 500; 800; 1000; 700].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hi.
      do 22 (destruct i; [
        simpl in Hi; try congruence; simpl; reflexivity
        | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply NoDup_Permutation.
        -- repeat (constructor; [ simpl; tauto | ]); apply NoDup_nil.
        -- repeat (constructor; [ simpl; tauto | ]); apply NoDup_nil.
        -- intros x. split; intro H;
           repeat (destruct H as [H | H]; [ rewrite H; simpl; tauto | ]);
           contradiction.
      * simpl.
        repeat (apply Sorted_cons; [ | first [ apply HdRel_nil | apply HdRel_cons; simpl; lia ] ]).
        apply Sorted_nil.
Qed.