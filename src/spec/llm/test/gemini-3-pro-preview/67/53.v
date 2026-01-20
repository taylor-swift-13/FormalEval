Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition is_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (48 <=? n)%nat && (n <=? 57)%nat.

Fixpoint parse_aux (s : string) (acc : Z) (reading : bool) : list Z :=
  match s with
  | EmptyString => if reading then [acc] else []
  | String c rest =>
      if is_digit c then
        let d := Z.of_nat (nat_of_ascii c - 48) in
        parse_aux rest (acc * 10 + d) true
      else
        if reading then acc :: parse_aux rest 0 false
        else parse_aux rest 0 false
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  let numbers := parse_aux s 0 false in
  n - fold_right Z.add 0 numbers.

Example fruit_distribution_example : fruit_distribution "5 apples and 5 oranges" 11 = 1.
Proof. reflexivity. Qed.