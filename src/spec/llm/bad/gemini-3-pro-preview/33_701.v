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

Definition le_string (s1 s2 : string) : Prop :=
  match String.compare s1 s2 with
  | Gt => False
  | _ => True
  end.

Definition sort_third_spec (l : list string) (res : list string) : Prop :=
  length res = length l /\
  (forall i : nat, (i mod 3 <> 0)%nat -> nth_error res i = nth_error l i) /\
  Permutation (extract_thirds res 0) (extract_thirds l 0) /\
  Sorted le_string (extract_thirds res 0).

Example test_case : sort_third_spec 
  ["KaTQ"; "DAxnifdXi"; "DAxnifdXi"; "DAxnifdXiBKRP"; "DAxnifdXi"; "VFE"; "BKRP"; "FlYijS"; "DAxnifdXi"]
  ["BKRP"; "DAxnifdXi"; "DAxnifdXi"; "DAxnifdXiBKRP"; "DAxnifdXi"; "VFE"; "KaTQ"; "FlYijS"; "DAxnifdXi"].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      repeat (destruct i as [|i]; [
        simpl in *;
        try (match goal with
             | H : _ <> 0 |- _ => exfalso; apply H; reflexivity
             end);
        try reflexivity 
      | ]).
      simpl. reflexivity.
    + split.
      * simpl. apply Permutation_refl.
      * simpl.
        apply Sorted_cons.
        -- apply Sorted_cons.
           ++ apply Sorted_cons.
              ** apply Sorted_nil.
              ** apply HdRel_nil.
           ++ apply HdRel_cons. simpl. I.
        -- apply HdRel_cons. simpl. I.
Qed.