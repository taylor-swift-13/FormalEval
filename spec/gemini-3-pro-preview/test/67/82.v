Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Init.Nat.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Import ListNotations.

Definition is_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in
  andb (leb 48 n) (leb n 57).

Fixpoint get_numbers (s : string) (in_num : bool) (curr : Z) : list Z :=
  match s with
  | EmptyString => if in_num then [curr] else []
  | String c s' =>
      if is_digit c then
        get_numbers s' true (curr * 10 + (Z.of_nat (nat_of_ascii c) - 48))
      else
        if in_num then curr :: (get_numbers s' false 0)
        else get_numbers s' false 0
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  let nums := get_numbers s false 0 in
  let sum := fold_right Z.add 0 nums in
  n - sum.

Example test_fruit_distribution: fruit_distribution "20 apples and 0 oranges" 25 = 5.
Proof. reflexivity. Qed.