Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition is_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (Nat.leb 48 n) && (Nat.leb n 57).

Definition digit_to_Z (c : ascii) : Z :=
  Z.of_nat (nat_of_ascii c - 48).

Fixpoint parse_numbers (s : string) (acc : option Z) : list Z :=
  match s with
  | EmptyString =>
      match acc with
      | Some n => [n]
      | None => []
      end
  | String c s' =>
      if is_digit c then
        let d := digit_to_Z c in
        match acc with
        | Some n => parse_numbers s' (Some (n * 10 + d))
        | None => parse_numbers s' (Some d)
        end
      else
        match acc with
        | Some n => n :: parse_numbers s' None
        | None => parse_numbers s' None
        end
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  let nums := parse_numbers s None in
  let sum := fold_left Z.add nums 0 in
  n - sum.

Example test_fruit_distribution : fruit_distribution "5 apples and 6 oranges" 21 = 10.
Proof.
  compute.
  reflexivity.
Qed.