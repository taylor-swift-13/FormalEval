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

Definition digit_to_Z (c : ascii) : Z :=
  Z.of_nat ((nat_of_ascii c) - 48)%nat.

Fixpoint sum_numbers (s : string) (curr : option Z) : Z :=
  match s with
  | EmptyString =>
      match curr with
      | Some n => n
      | None => 0
      end
  | String c s' =>
      if is_digit c then
        let d := digit_to_Z c in
        let next_val := match curr with
                        | Some n => n * 10 + d
                        | None => d
                        end in
        sum_numbers s' (Some next_val)
      else
        match curr with
        | Some n => n + sum_numbers s' None
        | None => sum_numbers s' None
        end
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  n - sum_numbers s None.

Example test_fruit_distribution: fruit_distribution "0 apples and 1 oranges" 13 = 12.
Proof.
  compute.
  reflexivity.
Qed.