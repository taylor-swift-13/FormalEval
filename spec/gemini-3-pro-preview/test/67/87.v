Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.Ascii.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition is_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (48 <=? n)%nat && (n <=? 57)%nat.

Fixpoint get_numbers (s : string) (current_num : option Z) : list Z :=
  match s with
  | EmptyString =>
      match current_num with
      | Some n => [n]
      | None => []
      end
  | String c s' =>
      if is_digit c then
        let digit := Z.of_nat (nat_of_ascii c) - 48 in
        match current_num with
        | Some n => get_numbers s' (Some (n * 10 + digit))
        | None => get_numbers s' (Some digit)
        end
      else
        match current_num with
        | Some n => n :: get_numbers s' None
        | None => get_numbers s' None
        end
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  let nums := get_numbers s None in
  let sum := fold_right Z.add 0 nums in
  n - sum.

Example test_fruit_distribution: fruit_distribution "1 apples and 99 oranges" 199 = 99.
Proof. reflexivity. Qed.