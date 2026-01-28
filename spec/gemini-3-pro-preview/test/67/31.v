Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition string_to_list (s : string) : list ascii :=
  let fix aux s :=
    match s with
    | EmptyString => []
    | String c s' => c :: aux s'
    end
  in aux s.

Definition is_digit (c : ascii) : bool :=
  let n := Z.of_nat (nat_of_ascii c) in
  (48 <=? n) && (n <=? 57).

Definition digit_to_Z (c : ascii) : Z :=
  let n := Z.of_nat (nat_of_ascii c) in
  n - 48.

Fixpoint parse_nums_aux (l : list ascii) (curr : option Z) : list Z :=
  match l with
  | [] => match curr with Some n => [n] | None => [] end
  | c :: rest =>
      if is_digit c then
        let d := digit_to_Z c in
        let next_val := match curr with Some v => v * 10 + d | None => d end in
        parse_nums_aux rest (Some next_val)
      else
        match curr with
        | Some v => v :: parse_nums_aux rest None
        | None => parse_nums_aux rest None
        end
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  let chars := string_to_list s in
  let nums := parse_nums_aux chars None in
  let sum := fold_right Z.add 0 nums in
  n - sum.

Example test_fruit_distribution : fruit_distribution "0 apples and 1 oranges" 2 = 1.
Proof.
  compute.
  reflexivity.
Qed.