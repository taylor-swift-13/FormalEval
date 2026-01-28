Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope Z_scope.

Fixpoint get_evens (l : list Z) : list Z :=
  match l with
  | [] => []
  | x :: [] => [x]
  | x :: _ :: tl => x :: get_evens tl
  end.

Definition sort_even_spec (l res : list Z) : Prop :=
  length l = length res /\
  (forall i : nat, (i < length l)%nat -> Nat.odd i = true -> nth i l 0 = nth i res 0) /\
  Permutation (get_evens l) (get_evens res) /\
  Sorted Z.le (get_evens res).

Example test_sort_even_case : sort_even_spec 
  [5; 3; -5; -4; 2; -3; 3; -9; 0; 23; 1; -10; 123; 5; -10] 
  [-10; 3; -5; -4; 0; -3; 1; -9; 2; 23; 3; -10; 5; 5; 123].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 15 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        apply NoDup_Permutation.
        -- repeat (constructor; [ intro H; simpl in H; repeat (destruct H as [H|H]; [ lia | ]); contradiction | ]).
           apply NoDup_nil.
        -- repeat (constructor; [ intro H; simpl in H; repeat (destruct H as [H|H]; [ lia | ]); contradiction | ]).
           apply NoDup_nil.
        -- intros x. split; intro H; simpl in H;
           repeat (destruct H as [H|H]; [ rewrite H; simpl; tauto | ]); contradiction.
      * simpl.
        repeat (apply Sorted_cons; [| simpl; try apply HdRel_cons; try apply HdRel_nil; lia]).
        apply Sorted_nil.
Qed.