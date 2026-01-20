Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.
Open Scope Z_scope.

Fixpoint extract_thirds (l : list Z) (i : nat) : list Z :=
  match l with
  | [] => []
  | x :: xs => 
      if (i mod 3 =? 0)%nat 
      then x :: extract_thirds xs (S i) 
      else extract_thirds xs (S i)
  end.

Definition sort_third_spec (l : list Z) (res : list Z) : Prop :=
  length res = length l /\
  (forall i : nat, (i mod 3 <> 0)%nat -> nth_error res i = nth_error l i) /\
  Permutation (extract_thirds res 0) (extract_thirds l 0) /\
  Sorted Z.le (extract_thirds res 0).

Example test_case : sort_third_spec 
  [300; 500; 6; 7; 8; 289; 20; -105; -277; 104; 200; 3; 0; 5; 700; -3; 900; 18; -901; 800; 1000; 0; -277] 
  [-901; 500; 6; -3; 8; 289; 0; -105; -277; 0; 200; 3; 7; 5; 700; 20; 900; 18; 104; 800; 1000; 300; -277].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      destruct (le_lt_dec 23 i) as [Hge | Hlt].
      * rewrite !nth_error_None_ge; auto; simpl; try assumption.
      * do 23 (destruct i; [ simpl in H; try (contradict H; reflexivity); simpl; reflexivity | ]).
        exfalso. apply (Nat.nlt_ge _ _ Hlt).
        do 23 apply le_n_S. apply le_0_n.
    + split.
      * simpl.
        eapply Permutation_trans. 2: (change ([300; 7; 20; 104; 0; -3; -901; 0]) with ([300; 7; 20; 104; 0; -3] ++ -901 :: [0]); apply Permutation_middle). apply Permutation_cons.
        eapply Permutation_trans. 2: (change ([300; 7; 20; 104; 0; -3; 0]) with ([300; 7; 20; 104; 0] ++ -3 :: [0]); apply Permutation_middle). apply Permutation_cons.
        eapply Permutation_trans. 2: (change ([300; 7; 20; 104; 0; 0]) with ([300; 7; 20; 104] ++ 0 :: [0]); apply Permutation_middle). apply Permutation_cons.
        eapply Permutation_trans. 2: (change ([300; 7; 20; 104; 0]) with ([300; 7; 20; 104] ++ 0 :: []); apply Permutation_middle). apply Permutation_cons.
        eapply Permutation_trans. 2: (change ([300; 7; 20; 104]) with ([300] ++ 7 :: [20; 104]); apply Permutation_middle). apply Permutation_cons.
        eapply Permutation_trans. 2: (change ([300; 20; 104]) with ([300] ++ 20 :: [104]); apply Permutation_middle). apply Permutation_cons.
        eapply Permutation_trans. 2: (change ([300; 104]) with ([300] ++ 104 :: []); apply Permutation_middle). apply Permutation_cons.
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [ apply HdRel_cons; apply Z.leb_le; reflexivity | ]).
        apply Sorted_nil.
Qed.