Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.
Open Scope string_scope.

Definition string_le (s1 s2 : string) : Prop :=
  match String.compare s1 s2 with
  | Gt => False
  | _ => True
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
  ["BKRP"; "KaTQ"; "DAxnifdXi"; "DAxnifdXi"; "DAxnifdXi"; "DAxnifdXiBKRP"; "FlYij"; "VFE"; "xDAxnifdXi"; "BKRP"; "FlYijS"; "DAxnifdXi"] 
  ["BKRP"; "KaTQ"; "DAxnifdXi"; "BKRP"; "DAxnifdXi"; "DAxnifdXiBKRP"; "DAxnifdXi"; "VFE"; "xDAxnifdXi"; "FlYij"; "FlYijS"; "DAxnifdXi"].
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
      * simpl. apply Permutation_refl.
      * unfold string_le. simpl. repeat constructor.
Qed.