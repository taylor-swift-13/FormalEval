Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition is_digit (c : ascii) : bool :=
  let n := Z.of_nat (nat_of_ascii c) in
  (48 <=? n) && (n <=? 57).

Definition digit_to_Z (c : ascii) : Z :=
  Z.of_nat (nat_of_ascii c) - 48.

Fixpoint parse_next_int (s : list ascii) (acc : Z) : Z * list ascii :=
  match s with
  | [] => (acc, [])
  | c :: rest =>
      if is_digit c then
        parse_next_int rest (acc * 10 + digit_to_Z c)
      else
        (acc, c :: rest)
  end.

Fixpoint extract_ints (s : list ascii) : list Z :=
  match s with
  | [] => []
  | c :: rest =>
      if is_digit c then
        let (n, rest') := parse_next_int rest (digit_to_Z c) in
        n :: extract_ints rest'
      else
        extract_ints rest
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  let chars := list_ascii_of_string s in
  let ints := extract_ints chars in
  n - fold_right Z.add 0 ints.

Example test_fruit_distribution : fruit_distribution "50 apples and 50 oranges" 199 = 99.
Proof. reflexivity. Qed.