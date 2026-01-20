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
  ["BKRP"; "KaTQ"; "DAxnifdXi"; "DAxnifdXi"; "DAxnifdXi"; "DAxnifdXiBKRP"; "VFE"; "xDAxnifdXi"; "BKRP"; "VFE"; "DAxnifdXi"; "VFE"] 
  ["BKRP"; "KaTQ"; "DAxnifdXi"; "DAxnifdXi"; "DAxnifdXi"; "DAxnifdXiBKRP"; "VFE"; "xDAxnifdXi"; "BKRP"; "VFE"; "DAxnifdXi"; "VFE"].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H. reflexivity.
    + split.
      * simpl. apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [| first [ apply HdRel_nil | apply HdRel_cons; simpl; exact I ] ]).
        apply Sorted_nil.
Qed.