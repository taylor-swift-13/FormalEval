
Require Import Coq.Lists.List.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Rbasic_fun.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.

Open Scope R_scope.

Definition sum_squares_spec (lst : list R) (sum : nat) : Prop :=
  sum = fold_right Nat.add 0 (map (fun x => Nat.pow (Nat.ceil x) 2) lst).
