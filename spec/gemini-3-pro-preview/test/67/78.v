Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope string_scope.
Open Scope Z_scope.

Fixpoint string_to_list (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => c :: string_to_list s'
  end.

Definition is_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (48 <=? n)%nat && (n <=? 57)%nat.

Definition digit_to_Z (c : ascii) : Z :=
  Z.of_nat (nat_of_ascii c) - 48.

Fixpoint parse_numbers (l : list ascii) (curr : option Z) : list Z :=
  match l with
  | [] => match curr with
          | Some n => [n]
          | None => []
          end
  | c :: rest =>
      if is_digit c then
        let d := digit_to_Z c in
        match curr with
        | Some n => parse_numbers rest (Some (n * 10 + d))
        | None => parse_numbers rest (Some d)
        end
      else
        match curr with
        | Some n => n :: parse_numbers rest None
        | None => parse_numbers rest None
        end
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  let nums := parse_numbers (string_to_list s) None in
  n - fold_right Z.add 0 nums.

Example test_fruit_distribution : fruit_distribution "50 apples and 50 oranges" 100 = 0.
Proof.
  compute.
  reflexivity.
Qed.