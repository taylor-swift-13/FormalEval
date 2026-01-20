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

Fixpoint parse_ints (s : string) (curr : option Z) : list Z :=
  match s with
  | EmptyString =>
      match curr with
      | Some n => [n]
      | None => []
      end
  | String c s' =>
      if is_digit c then
        let d := Z.of_nat (nat_of_ascii c - 48) in
        match curr with
        | Some n => parse_ints s' (Some (n * 10 + d))
        | None => parse_ints s' (Some d)
        end
      else
        match curr with
        | Some n => n :: parse_ints s' None
        | None => parse_ints s' None
        end
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  n - fold_right Z.add 0 (parse_ints s None).

Example test_fruit_distribution : fruit_distribution "10 apples and 0 oranges" 15 = 5.
Proof. reflexivity. Qed.