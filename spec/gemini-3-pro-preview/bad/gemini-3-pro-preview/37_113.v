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
  [-5; -7; 2; 10; 0; 9; 5; -3; 2; 8; 3; 7] 
  [-5; -7; 0; 10; 2; 9; 2; -3; 3; 8; 5; 7].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      (* Handle indices 0 through 11 individually *)
      do 12 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      (* Handle out of bounds *)
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Current: [-5; 2; 0; 5; 2; 3] *)
        (* Target:  [-5; 0; 2; 2; 3; 5] *)
        apply Permutation_cons. (* Match -5 *)
        etransitivity. apply Permutation_swap. (* Swap 2 and 0 *)
        apply Permutation_cons. (* Match 0 *)
        apply Permutation_cons. (* Match 2 *)
        etransitivity. apply Permutation_swap. (* Swap 5 and 2 *)
        apply Permutation_cons. (* Match 2 *)
        apply Permutation_swap. (* Swap 5 and 3 to get [3; 5] *)
        apply Permutation_refl.
      * (* 4. Sorted check *)
        simpl.
        repeat match goal with
        | |- Sorted _ [] => apply Sorted_nil
        | |- Sorted _ (_ :: _) => apply Sorted_cons
        | |- HdRel _ _ [] => apply HdRel_nil
        | |- HdRel _ _ (_ :: _) => apply HdRel_cons; simpl; lia
        end.
Qed.