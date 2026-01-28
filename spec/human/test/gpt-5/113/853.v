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
  match n with
  | 0 => "0"%string
  | 1 => "1"%string
  | 2 => "2"%string
  | 3 => "3"%string
  | 4 => "4"%string
  | 5 => "5"%string
  | 6 => "6"%string
  | 7 => "7"%string
  | 8 => "8"%string
  | 9 => "9"%string
  | 10 => "10"%string
  | 11 => "11"%string
  | 12 => "12"%string
  | 13 => "13"%string
  | 14 => "14"%string
  | 15 => "15"%string
  | 16 => "16"%string
  | 17 => "17"%string
  | 18 => "18"%string
  | 19 => "19"%string
  | 20 => "20"%string
  | 21 => "21"%string
  | 22 => "22"%string
  | 23 => "23"%string
  | 24 => "24"%string
  | 25 => "25"%string
  | 26 => "26"%string
  | _ => "10plus"%string
  end.

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
    ["9999999999999999999999999"%string;
     "99999999999999999999999999"%string;
     "00044444444444444444444444444444444444444444444444444444444444444000000000000"%string;
     "1111111111111111111111111"%string;
     "000000000000000"%string]
    ["the number of odd elements 25n the str25ng 25 of the 25nput."%string;
     "the number of odd elements 26n the str26ng 26 of the 26nput."%string;
     "the number of odd elements 0n the str0ng 0 of the 0nput."%string;
     "the number of odd elements 25n the str25ng 25 of the 25nput."%string;
     "the number of odd elements 0n the str0ng 0 of the 0nput."%string].
Proof.
  unfold problem_113_spec.
  simpl.
  reflexivity.
Qed.