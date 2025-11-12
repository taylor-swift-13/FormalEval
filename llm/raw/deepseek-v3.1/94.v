
Require Import List.
Require Import ZArith.
Require Import Znumtheory.
Require Import Ascii.
Require Import String.
Require Import Bool.

Definition is_prime (a : Z) : bool :=
  if Z.ltb a 2 then false
  else
    let sqrt_a := Z.sqrt a in
    negb (List.existsb (fun x => Z.eqb (Z.modulo a x) 0) 
          (List.map Z.of_nat (seq 2 (Z.to_nat (Z.sub sqrt_a 1))))).

Fixpoint sum_digits (n : Z) : Z :=
  match n with
  | 0 => 0
  | _ => Z.add (Z.modulo n 10) (sum_digits (Z.div n 10))
  end.

Definition skjkasdkd_spec (lst : list Z) (result : Z) : Prop :=
  exists prime_list,
    (forall x, In x prime_list -> is_prime x = true) /\
    (forall x, In x lst -> is_prime x = true -> In x prime_list) /\
    (exists max_prime,
        In max_prime prime_list /\
        (forall x, In x prime_list -> Z.le x max_prime) /\
        result = sum_digits max_prime).
