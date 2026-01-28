Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Fixpoint list_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => c :: (list_of_string s')
  end.

Definition is_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (48 <=? n)%nat && (n <=? 57)%nat.

Fixpoint parse_int_aux (s : list ascii) (acc : Z) : Z :=
  match s with
  | [] => acc
  | c :: rest => 
      let val := Z.of_nat (nat_of_ascii c - 48) in
      parse_int_aux rest (acc * 10 + val)
  end.

Definition parse_int (s : list ascii) : Z := parse_int_aux s 0.

Fixpoint extract_numbers (s : list ascii) (in_num : bool) (curr : list ascii) : list Z :=
  match s with
  | [] => if in_num then [parse_int (rev curr)] else []
  | c :: rest =>
      if is_digit c then
        extract_numbers rest true (c :: curr)
      else
        if in_num then
          (parse_int (rev curr)) :: extract_numbers rest false []
        else
          extract_numbers rest false []
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  let chars := list_of_string s in
  let nums := extract_numbers chars false [] in
  let sum_nums := fold_right Z.add 0 nums in
  n - sum_nums.

Example test_fruit_distribution: fruit_distribution "24 apples and 18 oranges" 49 = 7.
Proof. reflexivity. Qed.