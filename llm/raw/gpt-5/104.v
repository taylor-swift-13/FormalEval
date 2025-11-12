
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.

Fixpoint all_odd_digitsb (n : nat) : bool :=
  match n with
  | 0 => false
  | _ =>
      let d := Nat.modulo n 10 in
      let q := Nat.div n 10 in
      Nat.odd d && (if Nat.eqb q 0 then true else all_odd_digitsb q)
  end.

Definition unique_digits_spec (x : list nat) (res : list nat) : Prop :=
  Sorted le res /\ Permutation res (List.filter all_odd_digitsb x).
