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
  [4; -2; -12; -9; 23; 3; 11; 13; -10; 13; 4; 122; -12; 4] 
  [-12; -2; -12; -9; -10; 3; 4; 13; 4; 13; 11; 122; 23; 4].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      destruct i. { simpl in Hodd. discriminate Hodd. }
      destruct i. { simpl. reflexivity. }
      destruct i. { simpl in Hodd. discriminate Hodd. }
      destruct i. { simpl. reflexivity. }
      destruct i. { simpl in Hodd. discriminate Hodd. }
      destruct i. { simpl. reflexivity. }
      destruct i. { simpl in Hodd. discriminate Hodd. }
      destruct i. { simpl. reflexivity. }
      destruct i. { simpl in Hodd. discriminate Hodd. }
      destruct i. { simpl. reflexivity. }
      destruct i. { simpl in Hodd. discriminate Hodd. }
      destruct i. { simpl. reflexivity. }
      destruct i. { simpl in Hodd. discriminate Hodd. }
      destruct i. { simpl. reflexivity. }
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Input Evens: [4; -12; 23; 11; -10; 4; -12] *)
        (* Sorted Evens: [-12; -12; -10; 4; 4; 11; 23] *)
        
        (* Move 4 *)
        apply Permutation_trans with (4 :: [-12; -12; -10] ++ [4; 11; 23]).
        { apply perm_skip.
          (* Move -12 *)
          apply perm_skip.
          (* Move 23 *)
          apply Permutation_trans with (23 :: [-12; -10; 4; 11] ++ []).
          { apply perm_skip.
            (* Move 11 *)
            apply Permutation_trans with (11 :: [-12; -10; 4] ++ []).
            { apply perm_skip.
              (* Move -10 *)
              apply Permutation_trans with (-10 :: [-12] ++ [4]).
              { apply perm_skip.
                (* Move 4 *)
                apply Permutation_trans with (4 :: [-12] ++ []).
                { apply perm_skip. apply Permutation_refl. }
                { apply Permutation_middle. }
              }
              { apply Permutation_middle. }
            }
            { apply Permutation_middle. }
          }
          { apply Permutation_middle. }
        }
        { apply Permutation_middle. }
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [| simpl; try apply HdRel_nil; try (apply HdRel_cons; lia)]).
        apply Sorted_nil.
Qed.