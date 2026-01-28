Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition is_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in
  andb (48 <=? n)%nat (n <=? 57)%nat.

Definition char_to_Z (c : ascii) : Z :=
  Z.of_nat (nat_of_ascii c - 48).

Fixpoint parse_ints (s : string) (curr : option Z) : list Z :=
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
        | Some n => parse_ints s' (Some (n * 10 + d))
        | None => parse_ints s' (Some d)
        end
      else
        match curr with
        | Some n => n :: parse_ints s' None
        | None => parse_ints s' None
        end
  end.

Definition fruit_distribution (s : string) (total : Z) : Z :=
  let nums := parse_ints s None in
  let sum := fold_right Z.add 0 nums in
  total - sum.

Example test_fruit_distribution : fruit_distribution "97 apples and 1 oranges" 105 = 7.
Proof.
  compute.
  reflexivity.
Qed.