Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.
Open Scope string_scope.

Fixpoint extract_thirds (l : list string) (i : nat) : list string :=
  match l with
  | [] => []
  | x :: xs => 
      if (i mod 3 =? 0)%nat 
      then x :: extract_thirds xs (S i) 
      else extract_thirds xs (S i)
  end.

Definition string_le (s1 s2 : string) : Prop :=
  match String.compare s1 s2 with
  | Gt => False
  | _ => True
  end.

Definition sort_third_spec (l : list string) (res : list string) : Prop :=
  length res = length l /\
  (forall i : nat, (i mod 3 <> 0)%nat -> nth_error res i = nth_error l i) /\
  Permutation (extract_thirds res 0) (extract_thirds l 0) /\
  Sorted string_le (extract_thirds res 0).

Example test_case : sort_third_spec 
  ["BKRP"; "KaTQ"; "DAnxnifdXi"; "DAxnifdXi"; "DAxnifdXi"; "DAxnifdXiBKRP"; "BKDAxnifdXiRP"; "VFE"; "xDAxnifdXi"; "BKRP"; "FlYijS"; "DAxnifdXi"]
  ["BKDAxnifdXiRP"; "KaTQ"; "DAnxnifdXi"; "BKRP"; "DAxnifdXi"; "DAxnifdXiBKRP"; "BKRP"; "VFE"; "xDAxnifdXi"; "DAxnifdXi"; "FlYijS"; "DAxnifdXi"].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      repeat (match goal with
              | [ |- context[nth_error (_ :: _) _] ] => destruct i
              end; 
              simpl in *; 
              try (exfalso; apply H; reflexivity); 
              try reflexivity).
    + split.
      * simpl.
        apply Permutation_trans with (l' := "BKDAxnifdXiRP" :: "BKRP" :: "DAxnifdXi" :: "BKRP" :: []).
        { apply Permutation_trans with (l' := "BKRP" :: "BKDAxnifdXiRP" :: "DAxnifdXi" :: "BKRP" :: []).
          - apply perm_skip. apply perm_swap.
          - apply perm_swap. }
        apply perm_skip.
        apply perm_skip.
        apply perm_swap.
      * simpl.
        repeat (apply Sorted_cons || apply Sorted_nil || apply HdRel_cons || apply HdRel_nil).
        all: simpl; exact I.
Qed.