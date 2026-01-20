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

Fixpoint parse_int (s : string) (acc : Z) : Z :=
  match s with
  | EmptyString => acc
  | String c s' =>
      if is_digit c then
        parse_int s' (acc * 10 + (Z.of_nat (nat_of_ascii c) - 48))
      else acc
  end.

Fixpoint split (s : string) (curr : string) : list string :=
  match s with
  | EmptyString => if String.eqb curr "" then [] else [curr]
  | String c s' =>
      if (nat_of_ascii c =? 32)%nat then
        if String.eqb curr "" then split s' ""
        else curr :: split s' ""
      else split s' (curr ++ String c EmptyString)
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  let words := split s "" in
  let nums := filter (fun w => match w with String c _ => is_digit c | _ => false end) words in
  let sum := fold_right Z.add 0 (map (fun w => parse_int w 0) nums) in
  n - sum.

Example test_fruit_distribution : fruit_distribution "3 apples and 5 oranges" 13 = 5.
Proof. vm_compute. reflexivity. Qed.