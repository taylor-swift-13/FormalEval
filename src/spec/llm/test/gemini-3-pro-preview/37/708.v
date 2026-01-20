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

Example test_sort_even_case : sort_even_spec [1; 1; 1; 0; 0; 12; 1; 1; 1; 1; 1] [0; 1; 1; 0; 1; 12; 1; 1; 1; 1; 1].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      destruct i; [ simpl in Hodd; discriminate | ]. (* 0 *)
      destruct i; [ simpl; reflexivity | ]. (* 1 *)
      destruct i; [ simpl in Hodd; discriminate | ]. (* 2 *)
      destruct i; [ simpl; reflexivity | ]. (* 3 *)
      destruct i; [ simpl in Hodd; discriminate | ]. (* 4 *)
      destruct i; [ simpl; reflexivity | ]. (* 5 *)
      destruct i; [ simpl in Hodd; discriminate | ]. (* 6 *)
      destruct i; [ simpl; reflexivity | ]. (* 7 *)
      destruct i; [ simpl in Hodd; discriminate | ]. (* 8 *)
      destruct i; [ simpl; reflexivity | ]. (* 9 *)
      destruct i; [ simpl in Hodd; discriminate | ]. (* 10 *)
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* LHS: [1; 1; 0; 1; 1; 1], RHS: [0; 1; 1; 1; 1; 1] *)
        apply Permutation_trans with (l' := [1; 0; 1; 1; 1; 1]).
        -- apply perm_skip. apply perm_swap.
        -- apply perm_swap.
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [ | try (apply HdRel_cons; lia); try apply HdRel_nil ]).
        apply Sorted_nil.
Qed.