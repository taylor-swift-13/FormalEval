Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Arith.

Fixpoint tri_val (n : nat) : nat :=
  match n with
  | 0 => 1
  | 1 => 3
  | S (S k) =>
      if Nat.even (S (S k))
      then 1 + Nat.div (S (S k)) 2
      else tri_val (S k) + tri_val k + 1 + Nat.div (S (S (S k))) 2
  end.

Definition tri_spec (n : nat) (ans : list nat) : Prop :=
  length ans = S n /\ forall i, i <= n -> nth i ans 0 = tri_val i.