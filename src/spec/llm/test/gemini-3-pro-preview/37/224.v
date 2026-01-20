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

Example test_sort_even_case : sort_even_spec [-7; 2; 3; 4; 5; 6; 7; 10; 2; 4] [-7; 2; 2; 4; 3; 6; 5; 10; 7; 4].
Proof.
  unfold sort_even_spec.
  split.
  - (* Length *)
    simpl. reflexivity.
  - split.
    + (* Odd indices *)
      intros i Hlen Hodd.
      (* Check indices 0 to 9 individually *)
      do 10 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      (* For i >= 10, length condition fails *)
      simpl in Hlen. lia.
    + split.
      * (* Permutation *)
        simpl.
        apply perm_skip.
        (* [3; 5; 7; 2] is a cyclic shift of [2; 3; 5; 7] *)
        change ([3; 5; 7; 2]) with ([3; 5; 7] ++ [2]).
        change ([2; 3; 5; 7]) with ([2] ++ [3; 5; 7]).
        apply Permutation_app_comm.
      * (* Sorted *)
        simpl.
        repeat (apply Sorted_cons; [ | first [ apply HdRel_cons; lia | apply HdRel_nil ] ]).
        apply Sorted_nil.
Qed.