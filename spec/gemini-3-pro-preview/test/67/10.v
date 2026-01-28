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

Fixpoint parse_nat (s : string) (acc : nat) : nat :=
  match s with
  | EmptyString => acc
  | String c s' =>
      if is_digit c then parse_nat s' (acc * 10 + (nat_of_ascii c - 48))
      else acc
  end.

Definition string_to_Z (s : string) : Z :=
  Z.of_nat (parse_nat s 0).

Fixpoint is_numeric_str (s : string) : bool :=
  match s with
  | EmptyString => false
  | String c s' =>
      if is_digit c then
        match s' with
        | EmptyString => true
        | _ => is_numeric_str s'
        end
      else false
  end.

Fixpoint split_string (s : string) (cur : string) : list string :=
  match s with
  | EmptyString => if string_dec cur "" then [] else [cur]
  | String c s' =>
      if (nat_of_ascii c =? 32)%nat then
        if string_dec cur "" then split_string s' ""
        else cur :: split_string s' ""
      else split_string s' (cur ++ String c EmptyString)
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  let words := split_string s "" in
  let nums := filter is_numeric_str words in
  let sum := fold_right (fun w acc => string_to_Z w + acc) 0 nums in
  n - sum.

Example fruit_distribution_example : fruit_distribution "7 apples and 8 oranges" 30 = 15.
Proof.
  reflexivity.
Qed.