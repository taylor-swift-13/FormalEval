Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.
Open Scope string_scope.

Fixpoint string_le (s1 s2 : string) : Prop :=
  match s1, s2 with
  | EmptyString, _ => True
  | String _ _, EmptyString => False
  | String c1 s1', String c2 s2' =>
      if (Nat.ltb (nat_of_ascii c1) (nat_of_ascii c2)) then True
      else if (Nat.ltb (nat_of_ascii c2) (nat_of_ascii c1)) then False
      else string_le s1' s2'
  end.

Fixpoint extract_thirds (l : list string) (i : nat) : list string :=
  match l with
  | [] => []
  | x :: xs => 
      if (i mod 3 =? 0)%nat 
      then x :: extract_thirds xs (S i) 
      else extract_thirds xs (S i)
  end.

Definition sort_third_spec (l : list string) (res : list string) : Prop :=
  length res = length l /\
  (forall i : nat, (i mod 3 <> 0)%nat -> nth_error res i = nth_error l i) /\
  Permutation (extract_thirds res 0) (extract_thirds l 0) /\
  Sorted string_le (extract_thirds res 0).

Example test_case : sort_third_spec 
  ["BKRP"; "KaTQ"; "DAxnifdXi"; "aTQ"; "DAxnifdXi"; "DAxnifdXiBKRP"; "VFE"; "xDAxnifdXi"; "BKRP"; "VFE"; "DAxnifdXi"; "VFE"]
  ["BKRP"; "KaTQ"; "DAxnifdXi"; "VFE"; "DAxnifdXi"; "DAxnifdXiBKRP"; "VFE"; "xDAxnifdXi"; "BKRP"; "aTQ"; "DAxnifdXi"; "VFE"].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 12 (destruct i; [
        simpl; try reflexivity; try (exfalso; apply H; reflexivity)
        | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply Permutation_cons.
        apply perm_trans with (l' := ["VFE"; "aTQ"; "VFE"]).
        -- apply Permutation_cons. apply perm_swap.
        -- apply perm_swap.
      * simpl.
        repeat constructor.
        all: simpl; auto.
Qed.