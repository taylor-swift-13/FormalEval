Existing Coq output file content 
specification for the first test case `input = [[1%Z; 2%Z; 3%Z]], output = [1%Z; 2%Z; 3%Z]`:
```coq
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
  [500%Z; 6%Z; 7%Z; 290%Z; 3%Z; 8%Z; 289%Z; 20%Z; 104%Z; -277%Z; 104%Z; 200%Z; 3%Z; 4%Z; -8%Z; 700%Z; 290%Z; -2%Z; -901%Z; 18%Z; 1000%Z; 7%Z; 104%Z]
  [-901%Z; 6%Z; 7%Z; -277%Z; 3%Z; 8%Z; 3%Z; 20%Z; 104%Z; 7%Z; 104%Z; 200%Z; 289%Z; 4%Z; -8%Z; 290%Z; 290%Z; -2%Z; 500%Z; 18%Z; 1000%Z; 700%Z; 104%Z].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 23 (destruct i; [
        simpl in *;
        try (match goal with | H : (0 <> 0)%nat |- _ => elim H; reflexivity end);
        reflexivity
      | ]).
      simpl. reflexivity.
    + split.
      * vm_compute.
        apply NoDup_Permutation.
        -- repeat constructor; simpl; intros H; repeat destruct H as [H|H]; try discriminate.
        -- repeat constructor; simpl; intros H; repeat destruct H as [H|H]; try discriminate.
        -- intros x; split; intros Hx; simpl in Hx;
           repeat destruct Hx as [Hx | Hx]; subst; simpl; tauto.
      * vm_compute.
        repeat (apply Sorted_cons; [ | simpl; vm_compute; discriminate ]).
        apply Sorted_nil.
Qed.