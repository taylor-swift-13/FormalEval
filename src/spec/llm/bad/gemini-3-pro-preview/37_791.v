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
  [5; 3; 2; 5; -3; 3; -11; 0; 123; 0; -10; 3; 3; 3] 
  [-11; 3; -10; 5; -3; 3; 2; 0; 3; 0; 5; 3; 123; 3].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      do 14 (destruct i; [
        simpl in Hodd;
        match goal with
        | H : false = true |- _ => discriminate H
        | _ => simpl; reflexivity
        end
      | ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Match 5 *)
        transitivity (5 :: [-11; -10; -3; 2; 3] ++ [123]).
        2: simpl; apply Permutation_middle.
        apply perm_skip.
        (* Match 2 *)
        transitivity (2 :: [-11; -10; -3] ++ [3; 123]).
        2: simpl; apply Permutation_middle.
        apply perm_skip.
        (* Match -3 *)
        transitivity (-3 :: [-11; -10] ++ [3; 123]).
        2: simpl; apply Permutation_middle.
        apply perm_skip.
        (* Match -11 *)
        transitivity (-11 :: [] ++ [-10; 3; 123]).
        2: simpl; apply Permutation_middle.
        apply perm_skip.
        (* Match 123 *)
        transitivity (123 :: [-10; 3] ++ []).
        2: simpl; apply Permutation_middle.
        apply perm_skip.
        (* Match -10 *)
        transitivity (-10 :: [] ++ [3]).
        2: simpl; apply Permutation_middle.
        apply perm_skip.
        (* Match 3 *)
        apply Permutation_refl.
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [ apply HdRel_cons; lia | ]).
        apply Sorted_nil.
Qed.