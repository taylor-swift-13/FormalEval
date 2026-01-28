Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition is_digit (a : ascii) : bool :=
  let n := nat_of_ascii a in
  (48 <=? n)%nat && (n <=? 57)%nat.

Definition to_digit (a : ascii) : Z :=
  Z.of_nat (nat_of_ascii a - 48).

Fixpoint parse_ints (s : string) (curr : option Z) : list Z :=
  match s with
  | EmptyString =>
    match curr with
    | Some n => [n]
    | None => []
    end
  | String c s' =>
    if is_digit c then
      let d := to_digit c in
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
  let nums := parse_ints s None in
  n - fold_right Z.add 0 nums.

Example example_fruit_distribution : fruit_distribution "2 apples and 0 oranges" 6 = 4.
Proof.
  compute. reflexivity.
Qed.