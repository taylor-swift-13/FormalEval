
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Import ListNotations.

Fixpoint has_even_digit (n: nat) : bool :=
  match n with
  | 0 => false
  | _ =>
    let digit := n mod 10 in
    if Nat.even digit then true else has_even_digit (n / 10)
  end.

Definition no_even_digits (n: nat) : bool :=
  negb (has_even_digit n).

Fixpoint sorted_strict_increasing (l: list nat) : Prop :=
  match l with
  | [] | [_] => True
  | x :: y :: t => x < y /\ sorted_strict_increasing (y :: t)
  end.

Definition unique_digits_spec (x: list nat) (res: list nat) : Prop :=
  res = List.sort Nat.leb (filter no_even_digits x) /\
  Forall (fun n => no_even_digits n = true) res /\
  sorted_strict_increasing res.
