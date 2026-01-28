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

Example test_sort_even_case : sort_even_spec [5; -2; 1; -12; 4; 23; 2; 3; 11; 12; -9; 3; 3] [-9; -2; 1; -12; 2; 23; 3; 3; 4; 12; 5; 3; 11].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      destruct i as [|i]. { simpl in Hodd; discriminate. }
      destruct i as [|i]. { simpl; reflexivity. }
      destruct i as [|i]. { simpl in Hodd; discriminate. }
      destruct i as [|i]. { simpl; reflexivity. }
      destruct i as [|i]. { simpl in Hodd; discriminate. }
      destruct i as [|i]. { simpl; reflexivity. }
      destruct i as [|i]. { simpl in Hodd; discriminate. }
      destruct i as [|i]. { simpl; reflexivity. }
      destruct i as [|i]. { simpl in Hodd; discriminate. }
      destruct i as [|i]. { simpl; reflexivity. }
      destruct i as [|i]. { simpl in Hodd; discriminate. }
      destruct i as [|i]. { simpl; reflexivity. }
      destruct i as [|i]. { simpl in Hodd; discriminate. }
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Goal: Permutation [5; 1; 4; 2; 11; -9; 3] [-9; 1; 2; 3; 4; 5; 11] *)
        
        (* Move -9 to front *)
        assert (H1: Permutation [5; 1; 4; 2; 11; -9; 3] (-9 :: [5; 1; 4; 2; 11; 3])).
        { change [5; 1; 4; 2; 11; -9; 3] with ([5; 1; 4; 2; 11] ++ -9 :: [3]).
          apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_trans with (1 := H1). clear H1. apply Permutation_cons.
        
        (* Move 1 to front *)
        assert (H2: Permutation [5; 1; 4; 2; 11; 3] (1 :: [5; 4; 2; 11; 3])).
        { change [5; 1; 4; 2; 11; 3] with ([5] ++ 1 :: [4; 2; 11; 3]).
          apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_trans with (1 := H2). clear H2. apply Permutation_cons.
        
        (* Move 2 to front *)
        assert (H3: Permutation [5; 4; 2; 11; 3] (2 :: [5; 4; 11; 3])).
        { change [5; 4; 2; 11; 3] with ([5; 4] ++ 2 :: [11; 3]).
          apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_trans with (1 := H3). clear H3. apply Permutation_cons.
        
        (* Move 3 to front *)
        assert (H4: Permutation [5; 4; 11; 3] (3 :: [5; 4; 11])).
        { change [5; 4; 11; 3] with ([5; 4; 11] ++ 3 :: []).
          rewrite app_nil_r. apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_trans with (1 := H4). clear H4. apply Permutation_cons.
        
        (* Move 4 to front (swap 5 and 4) *)
        apply Permutation_swap. apply Permutation_cons.
        
        (* Remaining: [5; 11] ~ [5; 11] *)
        apply Permutation_refl.
        
      * (* 4. Sorted check *)
        simpl.
        repeat (constructor; simpl; try lia).
Qed.