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
  [5; 3; 7; 0; 2; -3; -10; 0; 123; 1; 0; -10; 1; -3; 1] 
  [-10; 3; 0; 0; 1; -3; 1; 0; 2; 1; 5; -10; 7; -3; 123].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      do 15 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Goal: Permutation [5; 7; 2; -10; 123; 0; 1; 1] [-10; 0; 1; 1; 2; 5; 7; 123] *)
        transitivity (5 :: [-10; 0; 1; 1; 2; 7; 123]).
        { apply Permutation_cons.
          transitivity (7 :: [-10; 0; 1; 1; 2; 123]).
          { apply Permutation_cons.
            transitivity (2 :: [-10; 0; 1; 1; 123]).
            { apply Permutation_cons.
              (* -10 matches head *)
              apply Permutation_cons.
              (* 123 needs move *)
              transitivity (123 :: [0; 1; 1]).
              { apply Permutation_cons.
                (* 0, 1, 1 matches *)
                apply Permutation_refl.
              }
              { apply Permutation_sym, Permutation_middle. }
            }
            { apply Permutation_sym, Permutation_middle. }
          }
          { apply Permutation_sym, Permutation_middle. }
        }
        { apply Permutation_sym, Permutation_middle. }
      * (* 4. Sorted check *)
        simpl.
        repeat constructor; try lia.
Qed.