Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition is_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (48 <=? n)%nat && (n <=? 57)%nat.

Definition char_to_Z (c : ascii) : Z :=
  Z.of_nat (nat_of_ascii c - 48).

Fixpoint parse_numbers (s : string) (curr : option Z) : list Z :=
  match s with
  | EmptyString =>
    match curr with
    | Some n => [n]
    | None => []
    end
  | String c s' =>
    if is_digit c then
      let d := char_to_Z c in
      match curr with
      | Some n => parse_numbers s' (Some (n * 10 + d))
      | None => parse_numbers s' (Some d)
      end
    else
      match curr with
      | Some n => n :: parse_numbers s' None
      | None => parse_numbers s' None
      end
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  let nums := parse_numbers s None in
  let sum := fold_left Z.add nums 0 in
  n - sum.

Example test_fruit_distribution_1 : fruit_distribution "0 apples and 0 oranges" 29 = 29.
Proof. reflexivity. Qed.