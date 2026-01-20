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
  [5; 2; -13; 3; -5; 2; -10; -2; 3; 2; -8; 0; -10; -9] 
  [-13; 2; -10; 3; -10; 2; -8; -2; -5; 2; 3; 0; 5; -9].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      do 14 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen; lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* 5 *)
        apply Permutation_Add. do 6 apply Add_cons. apply Add_head.
        (* -13 *)
        apply Permutation_Add. apply Add_head.
        (* -5 *)
        apply Permutation_Add. do 3 apply Add_cons. apply Add_head.
        (* -10 *)
        apply Permutation_Add. apply Add_head.
        (* 3 *)
        apply Permutation_Add. do 2 apply Add_cons. apply Add_head.
        (* -8 *)
        apply Permutation_Add. apply Add_cons. apply Add_head.
        (* -10 *)
        apply Permutation_Add. apply Add_head.
        apply Permutation_nil.
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [ | apply HdRel_cons; lia ]).
        apply Sorted_cons. apply Sorted_nil. apply HdRel_nil.
Qed.