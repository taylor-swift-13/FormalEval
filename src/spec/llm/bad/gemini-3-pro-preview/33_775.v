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

Definition input := ["KaTQ"; "DAxnifdXi"; "DAxnifdXi"; "DAxnifdXiBKRP"; "DAxnifdXi"; "VFE"; "BKRP"; "FlYijS"; "DAxnifdXi"; "DAxnifdXi"].
Definition output := ["BKRP"; "DAxnifdXi"; "DAxnifdXi"; "DAxnifdXi"; "DAxnifdXi"; "VFE"; "DAxnifdXiBKRP"; "FlYijS"; "DAxnifdXi"; "KaTQ"].

Example test_case : sort_third_spec input output.
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 11 (destruct i; [
        simpl in H |- *; try contradiction; try reflexivity
        | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        (* Target: ["BKRP"; "DAxnifdXi"; "DAxnifdXiBKRP"; "KaTQ"] *)
        (* Source: ["KaTQ"; "DAxnifdXiBKRP"; "BKRP"; "DAxnifdXi"] *)
        apply Permutation_trans with (l' := ["DAxnifdXiBKRP"; "KaTQ"; "BKRP"; "DAxnifdXi"]).
        { constructor 3. }
        apply Permutation_trans with (l' := ["DAxnifdXiBKRP"; "BKRP"; "KaTQ"; "DAxnifdXi"]).
        { apply Permutation_cons. constructor 3. }
        apply Permutation_trans with (l' := ["DAxnifdXiBKRP"; "BKRP"; "DAxnifdXi"; "KaTQ"]).
        { apply Permutation_cons. apply Permutation_cons. constructor 3. }
        apply Permutation_trans with (l' := ["BKRP"; "DAxnifdXiBKRP"; "DAxnifdXi"; "KaTQ"]).
        { constructor 3. }
        apply Permutation_trans with (l' := ["BKRP"; "DAxnifdXi"; "DAxnifdXiBKRP"; "KaTQ"]).
        { apply Permutation_cons. constructor 3. }
        apply Permutation_refl.
      * simpl.
        repeat constructor.
Qed.