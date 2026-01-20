
Require Import List.
Require Import Arith.
Require Import Bool.

Definition is_prime (a : nat) : Prop :=
  a >= 2 /\ forall x : nat, 2 <= x <= Nat.sqrt a -> a mod x <> 0.

Definition skjkasdkd_spec (lst : list nat) (result : nat) : Prop :=
  exists largest_prime : nat,
    In largest_prime lst /\
    is_prime largest_prime /\
    (forall x : nat, In x lst -> is_prime x -> x <= largest_prime) /\
    result = fold_right (fun d acc => acc + d) 0 (map (fun ch => Nat.of_ascii ch) (list_ascii_of_string (Nat.to_string largest_prime))).
