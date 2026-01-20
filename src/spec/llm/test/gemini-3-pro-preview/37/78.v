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

Example test_sort_even_case : sort_even_spec [3; 4; 2; 2; 1; 2] [1; 4; 2; 2; 3; 2].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      destruct i as [|i].
      * (* i = 0 *)
        simpl in Hodd. discriminate Hodd.
      * destruct i as [|i].
        -- (* i = 1 *)
           simpl. reflexivity.
        -- destruct i as [|i].
           ++ (* i = 2 *)
              simpl in Hodd. discriminate Hodd.
           ++ destruct i as [|i].
              ** (* i = 3 *)
                 simpl. reflexivity.
              ** destruct i as [|i].
                 --- (* i = 4 *)
                     simpl in Hodd. discriminate Hodd.
                 --- destruct i as [|i].
                     +++ (* i = 5 *)
                         simpl. reflexivity.
                     +++ (* i >= 6 *)
                         simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Target: Permutation [3; 2; 1] [1; 2; 3] *)
        apply perm_trans with (l' := [2; 3; 1]).
        { apply perm_swap. }
        apply perm_trans with (l' := [2; 1; 3]).
        { apply perm_skip. apply perm_swap. }
        apply perm_swap.
      * (* 4. Sorted check *)
        simpl.
        apply Sorted_cons.
        -- (* Tail [2; 3] is sorted *)
           apply Sorted_cons.
           ++ (* Tail [3] is sorted *)
              apply Sorted_cons.
              ** apply Sorted_nil.
              ** apply HdRel_nil.
           ++ (* Head relation: 2 <= 3 *)
              apply HdRel_cons. lia.
        -- (* Head relation: 1 <= 2 *)
           apply HdRel_cons. lia.
Qed.