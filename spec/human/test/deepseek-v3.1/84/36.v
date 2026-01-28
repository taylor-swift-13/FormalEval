Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.

Open Scope string_scope.

Fixpoint sum_decimal_digits_aux (fuel n : nat) : nat :=
  match fuel with
  | 0 => 0
  | S f' =>
    match n with
    | 0 => 0
    | _ => (n mod 10) + sum_decimal_digits_aux f' (n / 10)
    end
  end.

Definition sum_decimal_digits (n : nat) : nat :=
  sum_decimal_digits_aux n n.

Fixpoint nat_to_binary_string_pos_aux (fuel n : nat) : string :=
  match fuel with
  | 0 => ""
  | S f' =>
      if Nat.eqb n 0 then ""
      else nat_to_binary_string_pos_aux f' (n / 2) ++ (if Nat.eqb (n mod 2) 0 then "0" else "1")
  end.

Definition nat_to_binary_string (n : nat) : string :=
  if Nat.eqb n 0 then "0"
  else nat_to_binary_string_pos_aux n n.

Definition solve_impl (N : nat) : string :=
  nat_to_binary_string (sum_decimal_digits N).

Example test_case_9996 : solve_impl 9996 = "100001".
Proof.
  unfold solve_impl.
  (* Compute sum of decimal digits of 9996 *)
  (* 9 + 9 + 9 + 6 = 33 *)
  (* Sum decimal digits of 33 *)
  (* 3 + 3 = 6 *)
  (* sum_decimal_digits 9996 = 6 *)
  (* Binary of 6 is "110" *)
  (* But expected output is "100001" which is binary of 33, so check implementation *)
  unfold sum_decimal_digits.
  simpl.
  (* sum_decimal_digits 9996 *)
  (* Let's compute step by step *)
  (* sum_decimal_digits 9996 *)
  (* sum_decimal_digits_aux 9996 9996 *)
  (* 9996 mod 10 = 6, 9996 / 10 = 999 *)
  (* sum = 6 + sum_decimal_digits_aux 999 999 *)
  (* 999 mod 10 = 9, 999 / 10 = 99 *)
  (* sum = 6 + 9 + sum_decimal_digits_aux 99 99 *)
  (* 99 mod 10 = 9, 99 / 10 = 9 *)
  (* sum = 6 + 9 + 9 + sum_decimal_digits_aux 9 9 *)
  (* 9 mod 10 = 9, 9 / 10 = 0 *)
  (* sum = 6 + 9 + 9 + 9 + sum_decimal_digits_aux 0 0 *)
  (* sum_decimal_digits_aux 0 0 = 0 *)
  (* total sum = 6 + 9 + 9 + 9 = 33 *)
  (* result = 33 *)
  (* Now 33 in binary: "100001" *)
  (* Since sum of digits is 33, which in binary is "100001" *)
  (* Our current code computes sum_decimal_digits correctly, and the binary representation is correct *)
  (* Let's verify that the binary string generated is "100001" *)
  (* Compute nat_to_binary_string 33 *)
  (* Should produce "100001" *)
  reflexivity.
Qed.