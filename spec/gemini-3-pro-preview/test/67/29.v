Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition is_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (48 <=? n)%nat && (n <=? 57)%nat.

Fixpoint parse_Z (s : string) (acc : Z) : option Z :=
  match s with
  | EmptyString => Some acc
  | String c s' =>
      if is_digit c then
        parse_Z s' (acc * 10 + Z.of_nat (nat_of_ascii c - 48))
      else None
  end.

Definition string_to_Z (s : string) : option Z :=
  match s with
  | EmptyString => None
  | _ => parse_Z s 0
  end.

Fixpoint split_space (s : string) (curr : string) : list string :=
  match s with
  | EmptyString => if string_dec curr "" then [] else [curr]
  | String c s' =>
      if (nat_of_ascii c =? 32)%nat then
        if string_dec curr "" then split_space s' ""
        else curr :: split_space s' ""
      else split_space s' (curr ++ String c EmptyString)
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  let words := split_space s "" in
  let vals := map (fun w => match string_to_Z w with Some v => v | None => 0 end) words in
  n - fold_right Z.add 0 vals.

Example test_fruit_distribution:
  fruit_distribution "3 apples and 4 oranges" 30 = 23.
Proof.
  compute. reflexivity.
Qed.