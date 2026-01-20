
Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Init.Nat.
Require Import Coq.Arith.Div2.
Require Import Coq.Arith.PeanoNat.

Definition is_prime (a : nat) : bool :=
  if a <? 2 then false
  else
    let max_div := Nat.sqrt a in
    negb (existsb (fun x => Nat.eqb (Nat.modulo a x) 0) (seq 2 (max_div - 1 + 1))).

Definition prime_length_spec (s : string) (b : bool) : Prop :=
  b = is_prime (String.length s).
