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
  [5; 3; -5; 2; 3; -10; 0; 123; 1; -10] 
  [-5; 3; 0; 2; 1; -10; 3; 123; 5; -10].
Proof.
  unfold sort_even_spec.
  split.
  - (* Length check *)
    simpl. reflexivity.
  - split.
    + (* Odd indices check *)
      intros i Hlen Hodd.
      do 10 (destruct i; [ simpl in Hodd; try discriminate Hodd; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * (* Permutation check *)
        simpl.
        apply NoDup_Permutation.
        -- repeat (constructor; [ simpl; intro H; repeat destruct H; lia | ]). apply NoDup_nil.
        -- repeat (constructor; [ simpl; intro H; repeat destruct H; lia | ]). apply NoDup_nil.
        -- intros x. simpl. tauto.
      * (* Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [ | try apply HdRel_cons; try apply HdRel_nil; lia ]).
        apply Sorted_nil.
Qed.