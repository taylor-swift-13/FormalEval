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

Fixpoint string_to_Z_aux (s : string) (acc : Z) : option Z :=
  match s with
  | EmptyString => Some acc
  | String c s' =>
      if is_digit c then
        let d := Z.of_nat (nat_of_ascii c - 48) in
        string_to_Z_aux s' (acc * 10 + d)
      else None
  end.

Definition string_to_Z (s : string) : option Z :=
  match s with
  | EmptyString => None
  | _ => string_to_Z_aux s 0
  end.

Fixpoint split_string (s : string) (curr : string) : list string :=
  match s with
  | EmptyString => [curr]
  | String c s' =>
      if (nat_of_ascii c =? 32)%nat then
        curr :: split_string s' ""
      else
        split_string s' (curr ++ String c EmptyString)
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  let words := split_string s "" in
  let sum_fruits := fold_right (fun w acc => 
    match string_to_Z w with
    | Some z => z + acc
    | None => acc
    end) 0 words in
  n - sum_fruits.

Example test_fruit_distribution: fruit_distribution "20 apples and 0 oranges" 198 = 178.
Proof. reflexivity. Qed.