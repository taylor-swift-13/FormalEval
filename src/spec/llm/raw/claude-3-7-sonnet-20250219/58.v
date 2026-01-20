
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

Definition no_duplicates {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y}) (l : list A) : Prop :=
  forall x, count_occ eq_dec l x <= 1.

Fixpoint in_list {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y}) (x : A) (l : list A) : bool :=
  match l with
  | [] => false
  | h :: t => if eq_dec x h then true else in_list eq_dec x t
  end.

Definition common_spec (l1 l2 output : list nat) : Prop :=
  (* output is sorted *)
  Sorted Nat.leb output /\
  (* output has no duplicates *)
  no_duplicates Nat.eq_dec output /\
  (* every element in output is in l1 and in l2 *)
  (forall x, In x output -> In x l1 /\ In x l2) /\
  (* output contains all elements that are common to l1 and l2 *)
  (forall x, In x l1 -> In x l2 -> In x output).
