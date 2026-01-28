Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition is_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (48 <=? n)%nat && (n <=? 57)%nat.

Definition digit_to_Z (c : ascii) : Z :=
  Z.of_nat (nat_of_ascii c - 48).

Fixpoint parse_and_sum (chars : list ascii) (current_num : Z) (acc : Z) (in_num : bool) : Z :=
  match chars with
  | [] => if in_num then acc + current_num else acc
  | c :: rest =>
      if is_digit c then
        parse_and_sum rest (current_num * 10 + digit_to_Z c) acc true
      else
        if in_num then
          parse_and_sum rest 0 (acc + current_num) false
        else
          parse_and_sum rest 0 acc false
  end.

Fixpoint string_to_list (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => c :: string_to_list s'
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  let chars := string_to_list s in
  let sum := parse_and_sum chars 0 0 false in
  n - sum.

Example test_fruit_distribution: fruit_distribution "0 apples and 1 oranges" 8 = 7.
Proof. reflexivity. Qed.