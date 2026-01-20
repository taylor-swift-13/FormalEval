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

(* Helper for Permutation proof on concrete lists *)
Fixpoint remove_first (x : Z) (l : list Z) : list Z :=
  match l with
  | [] => []
  | y :: tl => if (x =? y)%Z then tl else y :: remove_first x tl
  end.

Lemma perm_remove_first : forall x l,
  In x l -> Permutation l (x :: remove_first x l).
Proof.
  intros x l H.
  induction l as [|y l' IH]; simpl in *.
  - contradiction.
  - destruct (Z.eqb_spec x y).
    + subst. apply Permutation_refl.
    + destruct H.
      * congruence.
      * apply Permutation_trans with (y :: x :: remove_first x l').
        -- apply Permutation_cons. apply IH. assumption.
        -- apply Permutation_swap.
Qed.

Ltac resolve_perm :=
  match goal with
  | |- Permutation [] [] => apply Permutation_nil
  | |- Permutation (?x :: ?xs) ?ys =>
      apply Permutation_trans with (l' := x :: remove_first x ys);
      [ apply perm_remove_first; simpl; tauto | apply Permutation_cons; resolve_perm ]
  end.

Ltac solve_sorted :=
  repeat (constructor; [ | simpl; try apply HdRel_nil; try (apply HdRel_cons; lia) ]).

Example test_case : sort_third_spec 
  [300; 500; 6; 7; 8; 289; 20; -105; -277; 104; 200; 3; 4; 5; 700; 900; -200; -901; 800; 1000] 
  [4; 500; 6; 7; 8; 289; 20; -105; -277; 104; 200; 3; 300; 5; 700; 800; -200; -901; 900; 1000].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices *)
      intros i H.
      (* We destruct i enough times to cover the list length (20) *)
      repeat (destruct i as [|i]; [ simpl in *; try congruence; try reflexivity | ]).
      (* Tail case where i >= 20 *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation *)
        simpl.
        resolve_perm.
      * (* 4. Sorted *)
        simpl.
        solve_sorted.
Qed.