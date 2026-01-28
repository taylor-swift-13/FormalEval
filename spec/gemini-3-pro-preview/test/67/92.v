Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope string_scope.
Open Scope Z_scope.

Definition is_digit (c : ascii) : bool :=
  let n := Z.of_nat (nat_of_ascii c) in
  (n >=? 48) && (n <=? 57).

Definition digit_val (c : ascii) : Z :=
  Z.of_nat (nat_of_ascii c) - 48.

Fixpoint parse_numbers (s : string) (curr : option Z) : list Z :=
  match s with
  | EmptyString =>
      match curr with
      | Some n => [n]
      | None => []
      end
  | String c s' =>
      if is_digit c then
        let d := digit_val c in
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
  n - fold_right Z.add 0 nums.

Example test_fruit_distribution : fruit_distribution "99 apples and 1 oranges" 106 = 6.
Proof.
  compute.
  reflexivity.
Qed.