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

Fixpoint extract_numbers_aux (s : string) (cur : option Z) : list Z :=
  match s with
  | EmptyString =>
      match cur with
      | Some n => [n]
      | None => []
      end
  | String c s' =>
      if is_digit c then
        let d := Z.of_nat (nat_of_ascii c - 48) in
        match cur with
        | Some n => extract_numbers_aux s' (Some (n * 10 + d))
        | None => extract_numbers_aux s' (Some d)
        end
      else
        match cur with
        | Some n => n :: extract_numbers_aux s' None
        | None => extract_numbers_aux s' None
        end
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  let nums := extract_numbers_aux s None in
  n - fold_right Z.add 0 nums.

Example test_fruit_distribution: fruit_distribution "1 apples and 0 oranges" 3 = 2.
Proof.
  simpl.
  reflexivity.
Qed.