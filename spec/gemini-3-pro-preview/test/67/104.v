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

Fixpoint parse_numbers (s : string) (acc : option Z) : list Z :=
  match s with
  | EmptyString =>
      match acc with
      | Some n => [n]
      | None => []
      end
  | String c s' =>
      if is_digit c then
        let d := char_to_Z c in
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
  n - fold_right Z.add 0 nums.

Example test_fruit_distribution : fruit_distribution "15 apples and 8 oranges" 198 = 175.
Proof. reflexivity. Qed.