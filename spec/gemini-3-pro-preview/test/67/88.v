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

Definition to_digit (c : ascii) : Z :=
  Z.of_nat (nat_of_ascii c - 48).

Fixpoint parse_int_aux (s : string) (acc : Z) : Z * string :=
  match s with
  | EmptyString => (acc, EmptyString)
  | String c s' =>
    if is_digit c then parse_int_aux s' (acc * 10 + to_digit c)
    else (acc, s)
  end.

Fixpoint extract_numbers (s : string) (fuel : nat) : list Z :=
  match fuel with
  | 0%nat => []
  | S fuel' =>
    match s with
    | EmptyString => []
    | String c s' =>
      if is_digit c then
        let (n, rem) := parse_int_aux s' (to_digit c) in
        n :: extract_numbers rem fuel'
      else extract_numbers s' fuel'
    end
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  let nums := extract_numbers s (String.length s) in
  n - fold_right Z.add 0 nums.

Example example_test_case : fruit_distribution "50 apples and 50 oranges" 200 = 100.
Proof.
  compute.
  reflexivity.
Qed.