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
  Z.of_nat ((nat_of_ascii c) - 48)%nat.

Fixpoint parse_ints (s : string) (curr : option Z) : list Z :=
  match s with
  | EmptyString => 
      match curr with
      | Some val => [val]
      | None => []
      end
  | String c s' =>
      if is_digit c then
        let d := digit_to_Z c in
        match curr with
        | Some val => parse_ints s' (Some (val * 10 + d))
        | None => parse_ints s' (Some d)
        end
      else
        match curr with
        | Some val => val :: (parse_ints s' None)
        | None => parse_ints s' None
        end
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  let nums := parse_ints s None in
  let sum := fold_right Z.add 0 nums in
  n - sum.

Example fruit_distribution_example : fruit_distribution "99 apples and 1 oranges" 104 = 4.
Proof.
  compute.
  reflexivity.
Qed.