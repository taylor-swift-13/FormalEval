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

Definition string_of_digit (n : nat) : string :=
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
  | _ => "X"%string
  end.

Definition nat_to_string (n : nat) : string :=
  if (n <? 10)%nat then string_of_digit n
  else if (n <? 20)%nat then "1"%string ++ string_of_digit (n - 10)
  else if (n <? 30)%nat then "2"%string ++ string_of_digit (n - 20)
  else if (n <? 40)%nat then "3"%string ++ string_of_digit (n - 30)
  else if (n <? 50)%nat then "4"%string ++ string_of_digit (n - 40)
  else if (n <? 60)%nat then "5"%string ++ string_of_digit (n - 50)
  else if (n <? 70)%nat then "6"%string ++ string_of_digit (n - 60)
  else if (n <? 80)%nat then "7"%string ++ string_of_digit (n - 70)
  else if (n <? 90)%nat then "8"%string ++ string_of_digit (n - 80)
  else if (n <? 100)%nat then "9"%string ++ string_of_digit (n - 90)
  else "overflow"%string.

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
    ["999999999999911111111999999999999"%string;
     "1111111111111111111111111"%string;
     "000000000000000"%string;
     "1111111111111111111111231111"%string;
     "99999999999995555555555555555555555559"%string;
     "33333333333333333333333333333"%string]
    ["the number of odd elements 33n the str33ng 33 of the 33nput."%string;
     "the number of odd elements 25n the str25ng 25 of the 25nput."%string;
     "the number of odd elements 0n the str0ng 0 of the 0nput."%string;
     "the number of odd elements 27n the str27ng 27 of the 27nput."%string;
     "the number of odd elements 38n the str38ng 38 of the 38nput."%string;
     "the number of odd elements 29n the str29ng 29 of the 29nput."%string].
Proof.
  unfold problem_113_spec.
  simpl.
  reflexivity.
Qed.