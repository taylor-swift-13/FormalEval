
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Import ListNotations.

Definition is_prime (a : nat) : Prop :=
  a >= 2 /\
  (forall x : nat, 2 <= x <= Nat.sqrt a -> x * x <= a -> a mod x <> 0).

Fixpoint sum_digits (n : nat) : nat :=
  match n with
  | 0 => 0
  | _ => (n mod 10) + sum_digits (n / 10)
  end.

Fixpoint list_max_prime (lst : list nat) : option nat :=
  match lst with
  | [] => None
  | x :: xs =>
    match list_max_prime xs with
    | None => if (a:=x) then if (existsb (fun d => Nat.modulo a d = 0) (seq 2 (Nat.sqrt a - 1))) then None else Some x else None
               (* simplified: use is_prime predicate below *)
             else None
    | Some p =>
      if (is_prime x) then Some (Nat.max x p) else Some p
    end
  end.

Definition skjkasdkd_spec (lst : list nat) (result : nat) : Prop :=
  exists p,
    In p lst /\
    is_prime p /\
    (forall q, In q lst -> is_prime q -> p >= q) /\
    result = sum_digits p.
