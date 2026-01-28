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
  [5; 0; 6; 0; 5; -12; 0; -5; 3] 
  [0; 0; 3; 0; 5; -12; 5; -5; 6].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      destruct i. { simpl in Hodd. discriminate. }
      destruct i. { simpl. reflexivity. } (* 1 *)
      destruct i. { simpl in Hodd. discriminate. } (* 2 *)
      destruct i. { simpl. reflexivity. } (* 3 *)
      destruct i. { simpl in Hodd. discriminate. } (* 4 *)
      destruct i. { simpl. reflexivity. } (* 5 *)
      destruct i. { simpl in Hodd. discriminate. } (* 6 *)
      destruct i. { simpl. reflexivity. } (* 7 *)
      destruct i. { simpl in Hodd. discriminate. } (* 8 *)
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Goal: Permutation [5; 6; 5; 0; 3] [0; 3; 5; 5; 6] *)
        
        (* Move 0 to front *)
        assert (H1: Permutation (0 :: [5; 6; 5] ++ [3]) ([5; 6; 5] ++ 0 :: [3])).
        { apply Permutation_middle. }
        simpl in H1.
        apply (Permutation_trans (Permutation_sym H1)). clear H1.
        apply perm_skip.
        
        (* Move 3 to front of rest: [5; 6; 5; 3] -> 3 :: [5; 6; 5] *)
        assert (H2: Permutation (3 :: [5; 6; 5] ++ []) ([5; 6; 5] ++ 3 :: [])).
        { apply Permutation_middle. }
        simpl in H2.
        apply (Permutation_trans (Permutation_sym H2)). clear H2.
        apply perm_skip.
        
        (* Sort [5; 6; 5] -> [5; 5; 6] *)
        apply perm_skip.
        apply perm_swap.
      * (* 4. Sorted check *)
        simpl.
        apply Sorted_cons.
        { apply Sorted_cons.
          { apply Sorted_cons.
            { apply Sorted_cons.
              { apply Sorted_cons.
                { apply Sorted_nil. }
                { apply HdRel_nil. }
              }
              { apply HdRel_cons. lia. }
            }
            { apply HdRel_cons. lia. }
          }
          { apply HdRel_cons. lia. }
        }
        { apply HdRel_cons. lia. }
Qed.