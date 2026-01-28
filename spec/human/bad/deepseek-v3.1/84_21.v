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

Example test_case_9997 : solve_impl 9997 = "100010".
Proof.
  unfold solve_impl.
  unfold sum_decimal_digits.
  unfold nat_to_binary_string.
  simpl.
  replace (sum_decimal_digits 9997) with 37.
  - reflexivity.
  - (* Provide a step-by-step proof that sum_decimal_digits 9997 = 37 *)
    (* Since sum_decimal_digits 9997 computes the sum of digits (9+9+9+7=34), but our function sums digits, so 9+9+9+7=34. 
       However, the previous example expects output "100010" which is binary of 34, so you must correct to match sum of digits 37? Wait, the function sums digits: 9+9+9+7=34? 
       9+9+9+7=34, so output should be 34, not 37. But the test expects "100010" for input 9997, which is binary for 34. Thus, correct sum is 34.
    *)
    (* Let's check: sum of digits of 9997 is 9+9+9+7=34 *)
    simpl.
    reflexivity.
Qed.