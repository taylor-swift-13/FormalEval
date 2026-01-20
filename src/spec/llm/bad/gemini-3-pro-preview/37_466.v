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
  [-7; 2; 3; 4; 5; 7; 10; 5; 10; -7; 7] 
  [-7; 2; 3; 4; 5; 7; 7; 5; 10; -7; 10].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      repeat (destruct i as [|i]; [ simpl in *; try discriminate; try reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        do 3 apply perm_skip.
        eapply Permutation_trans.
        2: apply perm_swap.
        apply perm_skip.
        apply perm_swap.
      * (* 4. Sorted check *)
        simpl.
        do 6 apply Sorted_cons.
        -- apply Sorted_nil.
        -- apply HdRel_nil.
        -- apply HdRel_cons; lia.
        -- apply HdRel_cons; lia.
        -- apply HdRel_cons; lia.
        -- apply HdRel_cons; lia.
        -- apply HdRel_cons; lia.
Qed.