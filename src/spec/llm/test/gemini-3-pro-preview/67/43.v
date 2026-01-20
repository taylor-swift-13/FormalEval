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

Fixpoint parse_int_aux (s : string) (acc : Z) : Z :=
  match s with
  | EmptyString => acc
  | String c s' =>
      if is_digit c then
        parse_int_aux s' (acc * 10 + (Z.of_nat (nat_of_ascii c) - 48))
      else acc
  end.

Definition parse_int (s : string) : Z := parse_int_aux s 0.

Fixpoint skip_digits (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => if is_digit c then skip_digits s' else s
  end.

Fixpoint skip_non_digits (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => if is_digit c then s else skip_non_digits s'
  end.

Fixpoint extract_numbers (s : string) (fuel : nat) : list Z :=
  match fuel with
  | 0%nat => []
  | S fuel' =>
      let s' := skip_non_digits s in
      match s' with
      | EmptyString => []
      | String _ _ =>
          let n := parse_int s' in
          let rest := skip_digits s' in
          n :: extract_numbers rest fuel'
      end
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  let nums := extract_numbers s (String.length s) in
  n - fold_right Z.add 0 nums.

Example test_fruit_distribution: fruit_distribution "0 apples and 1 oranges" 51 = 50.
Proof. reflexivity. Qed.