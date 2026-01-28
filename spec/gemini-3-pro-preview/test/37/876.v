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
  [5; 0; 5; -1; 5; 0; 5; 0; 0; 0] 
  [0; 0; 5; -1; 5; 0; 5; 0; 5; 0].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      (* Check indices 0 to 9 *)
      do 10 (destruct i; [ simpl in *; try discriminate Hodd; try reflexivity | ]).
      (* Indices >= 10 are out of bounds for length 10 *)
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* We need to prove Permutation [5; 5; 5; 5; 0] [0; 5; 5; 5; 5] *)
        (* This is a rotation, which is a special case of commutativity of append *)
        change [5; 5; 5; 5; 0] with ([5; 5; 5; 5] ++ [0]).
        change [0; 5; 5; 5; 5] with ([0] ++ [5; 5; 5; 5]).
        apply Permutation_app_comm.
      * (* 4. Sorted check *)
        simpl.
        (* Prove Sorted Z.le [0; 5; 5; 5; 5] *)
        repeat (apply Sorted_cons; [ | try (apply HdRel_cons; lia); try apply HdRel_nil ]).
        apply Sorted_nil.
Qed.