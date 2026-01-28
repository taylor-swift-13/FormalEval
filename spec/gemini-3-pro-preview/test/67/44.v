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

Definition digit_val (c : ascii) : Z :=
  Z.of_nat (nat_of_ascii c - 48).

Fixpoint extract_nums (s : string) (acc : option Z) : list Z :=
  match s with
  | EmptyString =>
      match acc with
      | Some n => [n]
      | None => []
      end
  | String c s' =>
      if is_digit c then
        let d := digit_val c in
        match acc with
        | Some n => extract_nums s' (Some (n * 10 + d))
        | None => extract_nums s' (Some d)
        end
      else
        match acc with
        | Some n => n :: extract_nums s' None
        | None => extract_nums s' None
        end
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  let nums := extract_nums s None in
  n - fold_right Z.add 0 nums.

Example test_fruit_distribution: fruit_distribution "2 apples and 0 oranges" 11 = 9.
Proof. reflexivity. Qed.