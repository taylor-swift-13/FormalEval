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
  [1; 2; 3; -3; 5; 1; 16; 16; -8; 9; -12; 7; 6; -13] 
  [-3; 2; 3; 1; 5; 1; 6; 16; -8; 9; -12; 7; 16; -13].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 20 (destruct i as [|i]; [ simpl in *; try congruence; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl. apply NoDup_Permutation.
        -- repeat (constructor; [ intro Hin; simpl in Hin; repeat destruct Hin as [Hin|Hin]; try discriminate | ]).
        -- repeat (constructor; [ intro Hin; simpl in Hin; repeat destruct Hin as [Hin|Hin]; try discriminate | ]).
        -- intros x. simpl. split; intros Hx; repeat destruct Hx as [Hx|Hx]; subst; auto; try contradiction.
      * simpl.
        repeat apply Sorted_cons.
        all: try apply Sorted_nil.
        all: try apply HdRel_nil.
        all: try (apply HdRel_cons; apply Z.leb_le; reflexivity).
Qed.