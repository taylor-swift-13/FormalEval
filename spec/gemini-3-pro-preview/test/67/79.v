Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

Definition is_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (48 <=? n)%nat && (n <=? 57)%nat.

Fixpoint string_to_list (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => c :: string_to_list s'
  end.

Fixpoint get_numbers (chars : list ascii) (current_num : option Z) : list Z :=
  match chars with
  | [] => match current_num with Some n => [n] | None => [] end
  | c :: rest =>
      if is_digit c then
        let d := Z.of_nat (nat_of_ascii c - 48) in
        let next_num := match current_num with
                        | Some n => n * 10 + d
                        | None => d
                        end in
        get_numbers rest (Some next_num)
      else
        match current_num with
        | Some n => n :: get_numbers rest None
        | None => get_numbers rest None
        end
  end.

Definition fruit_distribution (s : string) (total : Z) : Z :=
  let nums := get_numbers (string_to_list s) None in
  let sum := fold_right Z.add 0 nums in
  total - sum.

Example test_fruit_distribution : fruit_distribution "100 apples and 100 oranges" 200 = 0.
Proof. reflexivity. Qed.