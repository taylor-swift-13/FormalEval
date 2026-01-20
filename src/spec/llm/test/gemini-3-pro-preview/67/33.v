Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Fixpoint list_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => c :: list_of_string s'
  end.

Definition is_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (48 <=? n)%nat && (n <=? 57)%nat.

Definition digit_to_Z (c : ascii) : Z :=
  Z.of_nat (nat_of_ascii c - 48).

Fixpoint parse_numbers (l : list ascii) (acc : option Z) : list Z :=
  match l with
  | [] => match acc with
          | Some n => [n]
          | None => []
          end
  | c :: rest =>
      if is_digit c then
        let d := digit_to_Z c in
        match acc with
        | Some n => parse_numbers rest (Some (n * 10 + d))
        | None => parse_numbers rest (Some d)
        end
      else
        match acc with
        | Some n => n :: parse_numbers rest None
        | None => parse_numbers rest None
        end
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  let chars := list_of_string s in
  let nums := parse_numbers chars None in
  let sum := fold_right Z.add 0 nums in
  n - sum.

Example test_fruit_distribution: fruit_distribution "3 apples and 5 oranges" 10 = 2.
Proof.
  vm_compute.
  reflexivity.
Qed.