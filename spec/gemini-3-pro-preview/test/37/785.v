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

Example test_sort_even_case : sort_even_spec [-5; 2; -11; 2; 1; -5] [-11; 2; -5; 2; 1; -5].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      do 6 (destruct i; [ simpl in *; try discriminate; try reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* LHS evens: [-5; -11; 1], RHS evens: [-11; -5; 1] *)
        apply perm_swap.
      * (* 4. Sorted check *)
        simpl.
        apply Sorted_cons.
        -- (* Tail sorted check: [-5; 1] *)
           apply Sorted_cons.
           ++ (* Tail sorted check: [1] *)
              apply Sorted_cons.
              ** apply Sorted_nil.
              ** apply HdRel_nil.
           ++ (* Head relation: -5 <= 1 *)
              apply HdRel_cons. lia.
        -- (* Head relation: -11 <= -5 *)
           apply HdRel_cons. lia.
Qed.