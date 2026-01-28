Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.

Definition is_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (48 <=? n)%nat && (n <=? 57)%nat.

Definition char_to_Z (c : ascii) : Z :=
  Z.of_nat (nat_of_ascii c - 48).

Fixpoint extract_numbers_aux (s : string) (cur : Z) (in_num : bool) : list Z :=
  match s with
  | EmptyString => if in_num then [cur] else []
  | String c s' =>
    if is_digit c then
      extract_numbers_aux s' (cur * 10 + char_to_Z c) true
    else
      if in_num then cur :: extract_numbers_aux s' 0 false
      else extract_numbers_aux s' 0 false
  end.

Definition extract_numbers (s : string) : list Z :=
  extract_numbers_aux s 0 false.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  n - fold_right Z.add 0 (extract_numbers s).

Example test_fruit_distribution : fruit_distribution "10 apples and 5 oranges" 20 = 5.
Proof. reflexivity. Qed.