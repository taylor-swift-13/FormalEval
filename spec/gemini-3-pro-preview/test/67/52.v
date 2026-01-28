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

Fixpoint parse_aux (s : string) (acc : option Z) : list Z :=
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
        | Some n => parse_aux s' (Some (n * 10 + d))
        | None => parse_aux s' (Some d)
        end
      else
        match acc with
        | Some n => n :: parse_aux s' None
        | None => parse_aux s' None
        end
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  let nums := parse_aux s None in
  n - fold_right Z.add 0 nums.

Example test_fruit_distribution : fruit_distribution "0 apples and 1 oranges" 11 = 10.
Proof.
  compute.
  reflexivity.
Qed.