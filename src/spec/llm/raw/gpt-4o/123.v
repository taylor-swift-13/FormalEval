
Require Import List.
Require Import Arith.

Definition collatz_next (x : nat) : nat :=
  if Nat.even x then x / 2 else 3 * x + 1.

Fixpoint collatz_sequence (x : nat) : list nat :=
  match x with
  | 1 => [1]
  | _ => x :: collatz_sequence (collatz_next x)
  end.

Definition is_odd (x : nat) : bool := negb (Nat.even x).

Definition get_odd_collatz_spec (n : nat) (result : list nat) : Prop :=
  let seq := collatz_sequence n in
  result = sort Nat.leb (filter is_odd seq).
