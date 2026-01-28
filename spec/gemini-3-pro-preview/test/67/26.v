Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition is_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in
  andb (48 <=? n)%nat (n <=? 57)%nat.

Definition digit_to_Z (c : ascii) : Z :=
  Z.of_nat (nat_of_ascii c - 48).

Fixpoint parse_ints (s : string) (acc : option Z) : list Z :=
  match s with
  | EmptyString =>
      match acc with
      | Some n => [n]
      | None => []
      end
  | String c s' =>
      if is_digit c then
        let d := digit_to_Z c in
        let new_acc := match acc with
                       | Some n => n * 10 + d
                       | None => d
                       end in
        parse_ints s' (Some new_acc)
      else
        match acc with
        | Some n => n :: parse_ints s' None
        | None => parse_ints s' None
        end
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  let nums := parse_ints s None in
  n - fold_right Z.add 0 nums.

Example fruit_distribution_example : fruit_distribution "0 apples and 1 oranges" 12 = 11.
Proof.
  reflexivity.
Qed.