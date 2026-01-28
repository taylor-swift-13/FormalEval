Require Import Coq.Arith.Arith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope string_scope.

(* Provided Definitions *)

Fixpoint to_digits_fuel (n fuel : nat) : list nat :=
  match fuel with
  | O => []
  | S fuel' =>
      if (n <? 10)%nat then
        [n]
      else
        (to_digits_fuel (n / 10) fuel') ++ [n mod 10]
  end.

Definition to_digits (n : nat) : list nat :=
  if (n =? 0)%nat then
    [0]
  else
    to_digits_fuel n n.

Definition digit_to_string (d : nat) : string :=
  match d with
  | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4"
  | 5 => "5" | 6 => "6" | 7 => "7" | 8 => "8" | 9 => "9"
  | _ => ""
  end.

Fixpoint from_digits_to_string (l : list nat) : string :=
  match l with
  | [] => ""
  | h :: t => (digit_to_string h) ++ (from_digits_to_string t)
  end.

Definition circular_shift_impl (x : nat) (shift : nat) : string :=
  let digits := to_digits x in
  let len := length digits in
  if (x =? 0)%nat then
    "0"
  else
    if (len <? shift)%nat then
      from_digits_to_string (rev digits)
    else
      let effective_shift := shift mod len in
      if (effective_shift =? 0)%nat then
        from_digits_to_string digits
      else
        let split_point := len - effective_shift in
        let new_head := skipn split_point digits in
        let new_tail := firstn split_point digits in
        from_digits_to_string (new_head ++ new_tail).

Definition problem_65_pre (x : nat) (shift : nat) : Prop := True.

Definition problem_65_spec (x : nat) (shift : nat) (result : string) : Prop :=
  result = circular_shift_impl x shift.

(* Test Case Proof *)

Example test_circular_shift_100_2 : problem_65_spec 100 2 "001".
Proof.
  (* Unfold the specification definition *)
  unfold problem_65_spec.
  
  (* Unfold the implementation to expose the logic *)
  unfold circular_shift_impl.
  
  (* 
     We need to verify that circular_shift_impl 100 2 evaluates to "001".
     Since the inputs are concrete natural numbers (100 and 2), 
     we can use vm_compute to fully evaluate the function.
     
     Logic trace:
     1. to_digits 100 -> [1; 0; 0]
     2. len = 3
     3. shift = 2
     4. len < shift (3 < 2) is false.
     5. effective_shift = 2 mod 3 = 2.
     6. split_point = 3 - 2 = 1.
     7. new_head = skipn 1 [1; 0; 0] = [0; 0].
     8. new_tail = firstn 1 [1; 0; 0] = [1].
     9. new_list = [0; 0] ++ [1] = [0; 0; 1].
     10. from_digits_to_string [0; 0; 1] -> "0" ++ "0" ++ "1" -> "001".
  *)
  vm_compute.
  
  (* The goal is now "001" = "001", which is trivially true *)
  reflexivity.
Qed.