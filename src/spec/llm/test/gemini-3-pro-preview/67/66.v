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

Fixpoint extract_nums (s : string) (curr : option Z) : list Z :=
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
        | Some n => extract_nums s' (Some (n * 10 + d))
        | None => extract_nums s' (Some d)
        end
      else
        match curr with
        | Some n => n :: extract_nums s' None
        | None => extract_nums s' None
        end
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  let nums := extract_nums s None in
  let sum := fold_right Z.add 0 nums in
  n - sum.

Example fruit_distribution_test : fruit_distribution "2 apples and 0 oranges" 9 = 7.
Proof.
  reflexivity.
Qed.