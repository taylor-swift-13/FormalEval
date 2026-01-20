
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Init.Nat.

Local Open Scope string_scope.
Local Open Scope Z_scope.

(* Helper function to calculate the sum of decimal digits of a natural number *)
Fixpoint sum_digits_nat (n : nat) : nat :=
  match n with
  | 0%nat => 0%nat
  | _ => (n mod 10 + sum_digits_nat (n / 10))%nat
  end.

(* Helper function to convert a binary string to an integer *)
Fixpoint bin_string_to_Z (s : string) (acc : Z) : Z :=
  match s with
  | EmptyString => acc
  | String a rest =>
      if (Ascii.eqb a "0"%char) then bin_string_to_Z rest (2 * acc)
      else if (Ascii.eqb a "1"%char) then bin_string_to_Z rest (2 * acc + 1)
      else -1 (* Invalid character *)
  end.

(* Predicate to ensure the binary string is in canonical form (no leading zeros unless the number is 0) *)
Definition is_canonical_binary (s : string) : Prop :=
  match s with
  | String a rest =>
      if (Ascii.eqb a "0"%char) then 
        match rest with 
        | EmptyString => True 
        | _ => False 
        end
      else if (Ascii.eqb a "1"%char) then True
      else False
  | EmptyString => False
  end.

Definition solve_spec (N : Z) (result : string) : Prop :=
  let digit_sum := Z.of_nat (sum_digits_nat (Z.to_nat N)) in
  is_canonical_binary result /\
  bin_string_to_Z result 0 = digit_sum.
