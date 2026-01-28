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
  | 27 => "27"%string
  | 28 => "28"%string
  | 29 => "29"%string
  | 30 => "30"%string
  | 31 => "31"%string
  | 32 => "32"%string
  | 33 => "33"%string
  | 34 => "34"%string
  | 35 => "35"%string
  | 36 => "36"%string
  | 37 => "37"%string
  | 38 => "38"%string
  | 39 => "39"%string
  | 40 => "40"%string
  | 41 => "41"%string
  | 42 => "42"%string
  | 43 => "43"%string
  | 44 => "44"%string
  | 45 => "45"%string
  | 46 => "46"%string
  | 47 => "47"%string
  | 48 => "48"%string
  | 49 => "49"%string
  | 50 => "50"%string
  | 51 => "51"%string
  | 52 => "52"%string
  | 53 => "53"%string
  | 54 => "54"%string
  | 55 => "55"%string
  | 56 => "56"%string
  | 57 => "57"%string
  | 58 => "58"%string
  | 59 => "59"%string
  | 60 => "60"%string
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
    ["33333333333333333333333333333333333333333324680333333333333333333"%string;
     "000000000000000"%string;
     "33333333333333333333332468033333333"%string;
     "33333333333333333333333333333"%string;
     "1111111111111111111111111"%string]
    ["the number of odd elements 60n the str60ng 60 of the 60nput."%string;
     "the number of odd elements 0n the str0ng 0 of the 0nput."%string;
     "the number of odd elements 30n the str30ng 30 of the 30nput."%string;
     "the number of odd elements 29n the str29ng 29 of the 29nput."%string;
     "the number of odd elements 25n the str25ng 25 of the 25nput."%string].
Proof.
  unfold problem_113_spec.
  simpl.
  reflexivity.
Qed.