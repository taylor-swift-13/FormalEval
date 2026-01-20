Existing Coq output file content 
specification for the first test case `input = [[6%Z; 300%Z; 500%Z; 6%Z; 7%Z; 1001%Z; 8%Z; 289%Z; 20%Z; -105%Z; -277%Z; 104%Z; 200%Z; 3%Z; 0%Z; 5%Z; 700%Z; 900%Z; -276%Z; 18%Z; -901%Z; 800%Z; 1000%Z; 0%Z; -277%Z]], output = [-277%Z; 300%Z; 500%Z; -276%Z; 7%Z; 1001%Z; -105%Z; 289%Z; 20%Z; 5%Z; -277%Z; 104%Z; 6%Z; 3%Z; 0%Z; 6%Z; 700%Z; 900%Z; 8%Z; 18%Z; -901%Z; 200%Z; 1000%Z; 0%Z; 800%Z]`:
```coq
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

Fixpoint insert (z : Z) (l : list Z) : list Z :=
  match l with
  | [] => [z]
  | y :: ys => if Z.le_dec z y then z :: l else y :: insert z ys
  end.

Fixpoint sort (l : list Z) : list Z :=
  match l with
  | [] => []
  | x :: xs => insert x (sort xs)
  end.

Lemma insert_perm : forall x l, Permutation (x :: l) (insert x l).
Proof.
  intros x l. induction l as [|y l' IH]; simpl.
  - apply Permutation_refl.
  - destruct (Z.le_dec x y).
    + apply Permutation_refl.
    + apply Permutation_trans with (y :: x :: l').
      * apply Permutation_swap.
      * apply Permutation_cons. apply IH.
Qed.

Lemma sort_perm : forall l, Permutation l (sort l).
Proof.
  induction l as [|x l' IH]; simpl.
  - apply Permutation_refl.
  - apply Permutation_trans with (x :: sort l').
    + apply Permutation_cons. apply IH.
    + apply insert_perm.
Qed.

Example test_case : sort_third_spec 
  [6; 300; 500; 6; 7; 1001; 8; 289; 20; -105; -277; 104; 200; 3; 0; 5; 700; 900; -276; 18; -901; 800; 1000; 0; -277] 
  [-277; 300; 500; -276; 7; 1001; -105; 289; 20; 5; -277; 104; 6; 3; 0; 6; 700; 900; 8; 18; -901; 200; 1000; 0; 800].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      destruct (le_lt_dec 25 i) as [Hge | Hlt].
      * assert (Hlen1: length [-277; 300; 500; -276; 7; 1001; -105; 289; 20; 5; -277; 104; 6; 3; 0; 6; 700; 900; 8; 18; -901; 200; 1000; 0; 800] <= i) by (simpl; assumption).
        assert (Hlen2: length [6; 300; 500; 6; 7; 1001; 8; 289; 20; -105; -277; 104; 200; 3; 0; 5; 700; 900; -276; 18; -901; 800; 1000; 0; -277] <= i) by (simpl; assumption).
        apply nth_error_None in Hlen1.
        apply nth_error_None in Hlen2.
        rewrite Hlen1, Hlen2. reflexivity.
      * do 25 (destruct i; [ simpl in *; try (contradiction || reflexivity) | ]).
        exfalso. do 25 apply Nat.lt_S_n in Hlt. inversion Hlt.
    + split.
      * simpl.
        transitivity (sort [6; 6; 8; -105; 200; 5; -276; 800; -277]).
        -- vm_compute. apply Permutation_refl.
        -- apply Permutation_sym. apply sort_perm.
      * simpl.
        repeat (apply Sorted_cons; [ | first [ apply HdRel_nil | apply HdRel_cons; compute; intro Hc; discriminate Hc ] ]).
        apply Sorted_nil.
Qed.