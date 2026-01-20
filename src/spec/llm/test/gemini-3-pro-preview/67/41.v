Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition is_digit (c : ascii) : bool :=
  let z := Z.of_nat (nat_of_ascii c) in
  (z >=? 48) && (z <=? 57).

Definition digit_to_Z (c : ascii) : Z :=
  Z.of_nat (nat_of_ascii c) - 48.

Fixpoint parse_string (s : string) (curr : option Z) : list Z :=
  match s with
  | EmptyString =>
      match curr with
      | Some v => [v]
      | None => []
      end
  | String c s' =>
      if is_digit c then
        let d := digit_to_Z c in
        match curr with
        | Some v => parse_string s' (Some (v * 10 + d))
        | None => parse_string s' (Some d)
        end
      else
        match curr with
        | Some v => v :: parse_string s' None
        | None => parse_string s' None
        end
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  let nums := parse_string s None in
  let sum := fold_right Z.add 0 nums in
  n - sum.

Example test_fruit_distribution : fruit_distribution "3 apples and 4 oranges" 8 = 1.
Proof.
  compute.
  reflexivity.
Qed.