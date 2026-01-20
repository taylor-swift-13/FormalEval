Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition is_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in
  andb (48 <=? n)%nat (n <=? 57)%nat.

Definition digit_to_Z (c : ascii) : Z :=
  Z.of_nat (nat_of_ascii c - 48).

Fixpoint extract_ints_pass (s : list ascii) (curr : option Z) : list Z :=
  match s with
  | [] => match curr with Some n => [n] | None => [] end
  | c :: rest =>
      if is_digit c then
        let d := digit_to_Z c in
        match curr with
        | Some n => extract_ints_pass rest (Some (n * 10 + d))
        | None => extract_ints_pass rest (Some d)
        end
      else
        match curr with
        | Some n => n :: extract_ints_pass rest None
        | None => extract_ints_pass rest None
        end
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  let chars := list_ascii_of_string s in
  let nums := extract_ints_pass chars None in
  let sum := fold_left Z.add nums 0 in
  n - sum.

Example test_fruit_distribution : fruit_distribution "0 apples and 1 oranges" 1 = 0.
Proof. reflexivity. Qed.