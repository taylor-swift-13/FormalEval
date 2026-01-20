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

Definition to_digit (c : ascii) : Z :=
  Z.of_nat (nat_of_ascii c - 48).

Fixpoint parse_integers (s : string) (curr : option Z) : list Z :=
  match s with
  | EmptyString =>
      match curr with
      | Some n => [n]
      | None => []
      end
  | String c rest =>
      if is_digit c then
        let d := to_digit c in
        match curr with
        | Some n => parse_integers rest (Some (n * 10 + d))
        | None => parse_integers rest (Some d)
        end
      else
        match curr with
        | Some n => n :: parse_integers rest None
        | None => parse_integers rest None
        end
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  let nums := parse_integers s None in
  n - fold_right Z.add 0 nums.

Example test_fruit_distribution : fruit_distribution "3 apples and 4 oranges" 13 = 6.
Proof.
  reflexivity.
Qed.