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

Definition digit_to_Z (c : ascii) : Z :=
  Z.of_nat (nat_of_ascii c - 48).

Fixpoint parse_ints_aux (s : string) (curr : option Z) (acc : list Z) : list Z :=
  match s with
  | EmptyString => match curr with
                   | Some n => n :: acc
                   | None => acc
                   end
  | String c s' =>
      if is_digit c then
        let d := digit_to_Z c in
        let new_curr := match curr with
                        | Some n => n * 10 + d
                        | None => d
                        end in
        parse_ints_aux s' (Some new_curr) acc
      else
        match curr with
        | Some n => parse_ints_aux s' None (n :: acc)
        | None => parse_ints_aux s' None acc
        end
  end.

Definition parse_ints (s : string) : list Z :=
  parse_ints_aux s None [].

Definition fruit_distribution (s : string) (n : Z) : Z :=
  let nums := parse_ints s in
  n - fold_right Z.add 0 nums.

Example test_fruit_distribution : fruit_distribution "2 apples and 0 oranges" 13%Z = 11%Z.
Proof. compute. reflexivity. Qed.