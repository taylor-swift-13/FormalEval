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

Example test_sort_even_case : sort_even_spec [122; -3; 4; 3; 3; -4; 3; 3] [3; -3; 3; 3; 4; -4; 122; 3].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      do 8 (destruct i; [ simpl in *; try discriminate; try reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        replace [122; 4; 3; 3] with ([122] ++ [4; 3; 3]) by reflexivity.
        replace [3; 3; 4; 122] with ([3; 3; 4] ++ [122]) by reflexivity.
        apply Permutation_trans with ([4; 3; 3] ++ [122]).
        -- apply Permutation_app_comm.
        -- apply Permutation_app.
           ++ replace [4; 3; 3] with ([4] ++ [3; 3]) by reflexivity.
              replace [3; 3; 4] with ([3; 3] ++ [4]) by reflexivity.
              apply Permutation_app_comm.
           ++ apply Permutation_refl.
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons || apply Sorted_nil || apply HdRel_nil || (apply HdRel_cons; lia)).
Qed.