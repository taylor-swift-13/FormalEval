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

Definition to_digit (c : ascii) : Z :=
  Z.of_nat (nat_of_ascii c - 48).

Fixpoint extract_numbers (s : string) (curr : option Z) : list Z :=
  match s with
  | EmptyString =>
      match curr with
      | Some n => [n]
      | None => []
      end
  | String c s' =>
      if is_digit c then
        match curr with
        | Some n => extract_numbers s' (Some (n * 10 + to_digit c))
        | None => extract_numbers s' (Some (to_digit c))
        end
      else
        match curr with
        | Some n => n :: extract_numbers s' None
        | None => extract_numbers s' None
        end
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  let nums := extract_numbers s None in
  n - fold_right Z.add 0 nums.

Example test_fruit_distribution: fruit_distribution "5 apples and 5 oranges" 12 = 2.
Proof. reflexivity. Qed.