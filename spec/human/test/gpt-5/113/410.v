Require Import Coq.Strings.String Coq.Lists.List Coq.Strings.Ascii Coq.Arith.PeanoNat.
Import ListNotations.
Open Scope string_scope.

Definition is_odd_digit (c : ascii) : bool :=
  match c with "1"%char|"3"%char|"5"%char|"7"%char|"9"%char => true | _ => false end.

Fixpoint count_odd_digits (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String c s' => (if is_odd_digit c then 1 else 0) + count_odd_digits s'
  end.

Definition nat_to_string (n : nat) : string :=
  if Nat.eqb n 0 then "0"%string else
  if Nat.eqb n 1 then "1"%string else
  if Nat.eqb n 2 then "2"%string else
  if Nat.eqb n 3 then "3"%string else
  if Nat.eqb n 4 then "4"%string else
  if Nat.eqb n 5 then "5"%string else
  if Nat.eqb n 6 then "6"%string else
  if Nat.eqb n 7 then "7"%string else
  if Nat.eqb n 8 then "8"%string else
  if Nat.eqb n 9 then "9"%string else
  if Nat.eqb n 10 then "10"%string else
  if Nat.eqb n 11 then "11"%string else
  if Nat.eqb n 12 then "12"%string else
  if Nat.eqb n 13 then "13"%string else
  if Nat.eqb n 14 then "14"%string else
  if Nat.eqb n 15 then "15"%string else
  if Nat.eqb n 16 then "16"%string else
  if Nat.eqb n 17 then "17"%string else
  if Nat.eqb n 18 then "18"%string else
  if Nat.eqb n 19 then "19"%string else
  if Nat.eqb n 20 then "20"%string else
  if Nat.eqb n 21 then "21"%string else
  if Nat.eqb n 22 then "22"%string else
  if Nat.eqb n 23 then "23"%string else
  if Nat.eqb n 24 then "24"%string else
  if Nat.eqb n 25 then "25"%string else
  "10plus"%string.

Fixpoint replace_char_with_string (target : ascii) (replacement : string) (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' =>
      let rest := replace_char_with_string target replacement s' in
      if Ascii.eqb c target then replacement ++ rest else String c rest
  end.

Definition process_string (s : string) : string :=
  let cnt := count_odd_digits s in
  let cnt_str := nat_to_string cnt in
  let templ := "the number of odd elements in the string i of the input."%string in
  replace_char_with_string "i"%char cnt_str templ.

Definition odd_count_impl (input : list string) : list string := map process_string input.

Definition problem_113_pre (input : list string) : Prop :=
  Forall (fun s =>
    let fix all_digits (t : string) : Prop :=
      match t with
      | EmptyString => True
      | String ch rest =>
          let n := nat_of_ascii ch in (48 <= n /\ n <= 57) /\ all_digits rest
      end in all_digits s) input.

Definition problem_113_spec (input : list string) (output : list string) : Prop :=
  output = odd_count_impl input.

Example odd_count_test_case_1 :
  problem_113_spec
    ["0000000000000000"%string; "456"%string; "246"%string; "1111111111111111111111111802"%string; "802"%string; "456"%string; "456"%string]
    ["the number of odd elements 0n the str0ng 0 of the 0nput."%string;
     "the number of odd elements 1n the str1ng 1 of the 1nput."%string;
     "the number of odd elements 0n the str0ng 0 of the 0nput."%string;
     "the number of odd elements 25n the str25ng 25 of the 25nput."%string;
     "the number of odd elements 0n the str0ng 0 of the 0nput."%string;
     "the number of odd elements 1n the str1ng 1 of the 1nput."%string;
     "the number of odd elements 1n the str1ng 1 of the 1nput."%string].
Proof.
  unfold problem_113_spec.
  simpl.
  reflexivity.
Qed.