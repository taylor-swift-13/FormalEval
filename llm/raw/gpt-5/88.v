Require Import Coq.Lists.List.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Arith.

Definition sort_array_spec (array : list nat) (res : list nat) : Prop :=
  Permutation array res /\
  match array with
  | [] => res = []
  | x :: xs =>
      let y := List.last (x :: xs) x in
      if Nat.even (x + y)
      then Sorted (fun a b => b <= a) res
      else Sorted (fun a b => a <= b) res
  end.