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
  [2; 2; 3; 4; 7; 13; 123; 8; 2] 
  [2; 2; 2; 4; 3; 13; 7; 8; 123].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      repeat (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        apply perm_skip.
        apply Permutation_sym.
        assert (H_perm_head_tail: forall A (x:A) l, Permutation (x::l) (l++[x])).
        { intros A x l. induction l as [|y l' IH].
          - simpl. apply Permutation_refl.
          - simpl. transitivity (y :: x :: l').
            + apply perm_swap.
            + apply perm_skip. apply IH. }
        apply H_perm_head_tail.
      * simpl.
        repeat match goal with
        | |- Sorted ?R [] => apply Sorted_nil
        | |- Sorted ?R (_ :: _) => apply Sorted_cons
        | |- HdRel ?R ?a [] => apply HdRel_nil
        | |- HdRel ?R ?a (_ :: _) => apply HdRel_cons; simpl; try lia
        end.
Qed.