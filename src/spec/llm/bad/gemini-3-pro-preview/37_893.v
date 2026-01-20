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
  [5; 122; 5; 0; 5; 5; 0; 5; 5; 0; 0; 5] 
  [0; 122; 0; 0; 5; 5; 5; 5; 5; 0; 5; 5].
Proof.
  unfold sort_even_spec.
  split.
  - reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 12 (destruct i; [
        simpl in Hodd; try discriminate Hodd;
        simpl; reflexivity
      | ]).
      simpl in Hlen; lia.
    + split.
      * vm_compute get_evens.
        apply Permutation_sym.
        change [5; 5; 5; 0; 5; 0] with ([5; 5; 5] ++ 0 :: [5; 0]).
        apply Permutation_cons_app.
        simpl.
        change [5; 5; 5; 5; 0] with ([5; 5; 5; 5] ++ 0 :: []).
        apply Permutation_cons_app.
        simpl.
        apply Permutation_refl.
      * vm_compute get_evens.
        repeat (apply Sorted_cons; [| apply HdRel_cons; lia]).
        apply Sorted_nil.
Qed.