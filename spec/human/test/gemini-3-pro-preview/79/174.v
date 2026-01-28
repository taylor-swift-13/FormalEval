Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope string_scope.
Open Scope Z_scope.

(* 
 * @brief Helper function to convert Z to binary string representation.
 * Note: The recursion is bounded by 'fuel' to satisfy Coq's termination checker.
 * We use Z for the input to handle large integers.
 *)
Fixpoint nat_to_binary_string_aux (n : Z) (fuel : nat) : string :=
  match fuel with
  | O => ""
  | S fuel' =>
      if n =? 0 then "0"
      else if n =? 1 then "1"
      else
        let bit := if Z.even n then "0" else "1" in
        nat_to_binary_string_aux (n / 2) fuel' ++ bit
  end.

(* 
 * @brief Wrapper for the binary conversion.
 * Handles 0 explicitly and sets initial fuel based on the logarithm of n.
 *)
Definition nat_to_binary_string (n : Z) : string :=
  if n =? 0 then "0"
  else nat_to_binary_string_aux n (Z.to_nat (Z.log2 n) + 2).

(* 
 * @brief Main implementation matching the specification.
 * Adds "db" prefix and suffix.
 *)
Definition decimal_to_binary_impl (decimal : Z) : string :=
  "db" ++ nat_to_binary_string decimal ++ "db".
  
Definition problem_79_pre (decimal : Z) : Prop := True.

Definition problem_79_spec (decimal : Z) (output : string) : Prop :=
  output = decimal_to_binary_impl decimal.

(* Test case verification *)
Example test_decimal_to_binary_huge : problem_79_spec 9999999999999999999999999999996 "db1111110001101111011111000100000001000101100000010010001010010110010011001111111111111111111111111111100db".
Proof.
  (* Use vm_compute to handle the large integer computation efficiently *)
  vm_compute.
  reflexivity.
Qed.