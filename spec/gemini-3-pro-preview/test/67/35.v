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

Definition digit_to_Z (c : ascii) : Z :=
  Z.of_nat (nat_of_ascii c - 48).

Fixpoint extract_numbers_aux (l : list ascii) (acc : option Z) : list Z :=
  match l with
  | [] => match acc with
          | Some n => [n]
          | None => []
          end
  | c :: rest =>
      if is_digit c then
        let d := digit_to_Z c in
        let new_acc := match acc with
                       | Some n => n * 10 + d
                       | None => d
                       end in
        extract_numbers_aux rest (Some new_acc)
      else
        match acc with
        | Some n => n :: extract_numbers_aux rest None
        | None => extract_numbers_aux rest None
        end
  end.

Definition extract_numbers (s : string) : list Z :=
  extract_numbers_aux (list_ascii_of_string s) None.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  n - fold_right Z.add 0 (extract_numbers s).

Example test_fruit_distribution: fruit_distribution "0 apples and 1 oranges" 9 = 8.
Proof.
  reflexivity.
Qed.