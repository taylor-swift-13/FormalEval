Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition is_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in
  andb (48 <=? n)%nat (n <=? 57)%nat.

Fixpoint parse_number (s : string) (acc : Z) : Z * string :=
  match s with
  | EmptyString => (acc, EmptyString)
  | String c s' =>
      if is_digit c then
        parse_number s' (acc * 10 + (Z.of_nat (nat_of_ascii c) - 48))
      else
        (acc, s)
  end.

Fixpoint extract_numbers_aux (fuel : nat) (s : string) : list Z :=
  match fuel with
  | 0%nat => []
  | S fuel' =>
      match s with
      | EmptyString => []
      | String c s' =>
          if is_digit c then
            let (num, rest) := parse_number s' (Z.of_nat (nat_of_ascii c) - 48) in
            num :: extract_numbers_aux fuel' rest
          else
            extract_numbers_aux fuel' s'
      end
  end.

Definition extract_numbers (s : string) : list Z :=
  extract_numbers_aux (String.length s) s.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  n - fold_right Z.add 0 (extract_numbers s).

Example test_fruit_distribution : fruit_distribution "24 apples and 18 oranges" 50 = 8.
Proof.
  reflexivity.
Qed.