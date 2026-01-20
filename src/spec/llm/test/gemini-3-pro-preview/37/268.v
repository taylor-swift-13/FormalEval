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
  [5; 2; -13; 3; -5; 2; -10; -3; -2; 3; -8; 0; 1; -10; -9] 
  [-13; 2; -10; 3; -9; 2; -8; -3; -5; 3; -2; 0; 1; -10; 5].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 15 (destruct i; [ simpl; try reflexivity; simpl in Hodd; try discriminate | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        apply NoDup_Permutation.
        -- repeat (constructor; [ intro Fin; simpl in Fin; repeat (destruct Fin as [Fin | Fin]; [ try lia | ]); contradiction | ]). apply NoDup_nil.
        -- repeat (constructor; [ intro Fin; simpl in Fin; repeat (destruct Fin as [Fin | Fin]; [ try lia | ]); contradiction | ]). apply NoDup_nil.
        -- intro x. simpl. split; intro H; repeat (destruct H as [H | H]; [ subst; tauto | ]); contradiction.
      * simpl.
        repeat (apply Sorted_cons; [| simpl; try apply HdRel_cons; try apply HdRel_nil; try lia]).
        apply Sorted_nil.
Qed.