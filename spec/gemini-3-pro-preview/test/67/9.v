Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition is_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (48 <=? n)%nat && (n <=? 57)%nat.

Fixpoint extract_numbers (s : string) (current_num : option Z) : list Z :=
  match s with
  | EmptyString => 
      match current_num with
      | Some n => [n]
      | None => []
      end
  | String c s' =>
      if is_digit c then
        let d := Z.of_nat (nat_of_ascii c - 48) in
        match current_num with
        | Some n => extract_numbers s' (Some (n * 10 + d))
        | None => extract_numbers s' (Some d)
        end
      else
        match current_num with
        | Some n => n :: extract_numbers s' None
        | None => extract_numbers s' None
        end
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  let nums := extract_numbers s None in
  let sum := fold_right Z.add 0 nums in
  n - sum.

Example fruit_distribution_example : fruit_distribution "3 apples and 4 oranges" 9 = 2.
Proof. reflexivity. Qed.