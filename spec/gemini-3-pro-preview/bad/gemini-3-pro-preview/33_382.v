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
  [300; 500; 6; 7; 289; 20; -105; -277; 200; 19; 3; 0; 5; 700; -3; 900; 18; -901; 800; 1001; 0; -277] 
  [-277; 500; 6; -105; 289; 20; 5; -277; 200; 7; 3; 0; 19; 700; -3; 300; 18; -901; 800; 1001; 0; 900].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      do 22 (destruct i; [ simpl in *; try congruence; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        apply NoDup_Permutation.
        -- repeat (constructor; [ simpl; intros [H1|H1]; try discriminate H1; try contradiction | ]).
           apply NoDup_nil.
        -- repeat (constructor; [ simpl; intros [H1|H1]; try discriminate H1; try contradiction | ]).
           apply NoDup_nil.
        -- intros x. split; intro Hx; simpl in Hx; 
           repeat (destruct Hx as [Hx|Hx]; [ subst; simpl; tauto | ]); try contradiction.
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat (apply Sorted_cons; [| apply HdRel_cons; [ vm_compute; reflexivity | ] || apply HdRel_nil]).
        apply Sorted_nil.
Qed.