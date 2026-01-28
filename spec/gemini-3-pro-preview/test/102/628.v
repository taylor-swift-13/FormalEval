Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint sum_digits_nat (n : nat) (fuel : nat) : nat :=
  match fuel with
  | 0%nat => 0%nat
  | S fuel' =>
    match n with
    | 0%nat => 0%nat
    | _ => (Nat.modulo n 10 + sum_digits_nat (Nat.div n 10) fuel')%nat
    end
  end.

Definition digit_sum (n : Z) : Z :=
  Z.of_nat (sum_digits_nat (Z.to_nat n) (Z.to_nat n)).

Fixpoint is_prime_aux (n : Z) (i : nat) : bool :=
  match i with
  | 0%nat | 1%nat => true
  | S i' =>
      let val := Z.of_nat i in
      if (n mod val =? 0) then false
      else is_prime_aux n i'
  end.

Definition is_prime (n : Z) : bool :=
  if n <? 2 then false
  else is_prime_aux n (Z.to_nat (Z.sqrt n)).

Definition skjkasdkd (l : list Z) : Z :=
  let primes := filter is_prime l in
  match primes with
  | [] => -1
  | h :: t => 
      let max_prime := fold_right Z.max h t in
      digit_sum max_prime
  end.

Example test_skjkasdkd_2: skjkasdkd [999; 100] = -1.
Proof. reflexivity. Qed.