Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition is_digit (c : ascii) : bool :=
  let n := Z.of_nat (nat_of_ascii c) in
  (48 <=? n) && (n <=? 57).

Definition to_digit (c : ascii) : Z :=
  Z.of_nat (nat_of_ascii c) - 48.

Fixpoint parse_aux (s : string) (curr : Z) (building : bool) : list Z :=
  match s with
  | EmptyString => if building then [curr] else []
  | String c s' =>
      if is_digit c then
        parse_aux s' (curr * 10 + to_digit c) true
      else
        if building then curr :: parse_aux s' 0 false
        else parse_aux s' 0 false
  end.

Definition fruit_distribution (s : string) (total : Z) : Z :=
  let nums := parse_aux s 0 false in
  total - fold_right Z.add 0 nums.

Example test_fruit_distribution:
  fruit_distribution "99 apples and 1 oranges" 105 = 5.
Proof.
  vm_compute.
  reflexivity.
Qed.