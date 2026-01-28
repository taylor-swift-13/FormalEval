Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Micromega.Lia.
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

Lemma perm_move : forall (A : Type) (x : A) (l l1 l2 : list A), 
  Permutation l (l1 ++ l2) -> Permutation (x :: l) (l1 ++ x :: l2).
Proof.
  intros. apply Permutation_trans with (x :: l1 ++ l2).
  - apply Permutation_cons. assumption.
  - apply Permutation_middle.
Qed.

Example test_case : sort_third_spec 
  [300; 500; 6; 7; 289; 20; 899; -105; -277; 104; 200; 3; 4; 5; 700; 900; -200; -104; -901; 800; 29; 5] 
  [-901; 500; 6; 4; 289; 20; 5; -105; -277; 7; 200; 3; 104; 5; 700; 300; -200; -104; 899; 800; 29; 900].
Proof.
  unfold sort_third_spec.
  split.
  - (* length *)
    simpl. reflexivity.
  - split.
    + (* indices preservation *)
      intros i H.
      (* Check for indices 0 to 21 *)
      do 22 (destruct i; [ simpl in H; try congruence; simpl; reflexivity | ]).
      (* For i >= 22 *)
      simpl. reflexivity.
    + split.
      * (* Permutation *)
        simpl.
        (* Goal: Permutation of sorted thirds vs original thirds *)
        (* Sorted: [-901; 4; 5; 7; 104; 300; 899; 900] *)
        (* Original: [300; 7; 899; 104; 4; 900; -901; 5] *)
        apply perm_move with (l1 := [300; 7; 899; 104; 4; 900]) (l2 := [5]).
        simpl.
        apply perm_move with (l1 := [300; 7; 899; 104]) (l2 := [900; 5]).
        simpl.
        apply perm_move with (l1 := [300; 7; 899; 104; 900]) (l2 := []).
        simpl. rewrite app_nil_r.
        apply perm_move with (l1 := [300]) (l2 := [899; 104; 900]).
        simpl.
        apply perm_move with (l1 := [300; 899]) (l2 := [900]).
        simpl.
        apply perm_move with (l1 := []) (l2 := [899; 900]).
        simpl.
        apply perm_move with (l1 := []) (l2 := [900]).
        simpl.
        apply perm_move with (l1 := []) (l2 := []).
        simpl. apply Permutation_nil.
      * (* Sorted *)
        simpl.
        repeat (constructor; try lia).
Qed.