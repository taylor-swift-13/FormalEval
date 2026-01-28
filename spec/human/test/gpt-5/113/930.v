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

Definition digit_to_string (n : nat) : string :=
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
  | _ => "?"%string
  end.

Definition nat_to_string (n : nat) : string :=
  if Nat.ltb n 10 then digit_to_string n
  else if Nat.ltb n 20 then "1"%string ++ digit_to_string (n - 10)
  else if Nat.ltb n 30 then "2"%string ++ digit_to_string (n - 20)
  else if Nat.ltb n 40 then "3"%string ++ digit_to_string (n - 30)
  else if Nat.ltb n 50 then "4"%string ++ digit_to_string (n - 40)
  else if Nat.ltb n 60 then "5"%string ++ digit_to_string (n - 50)
  else if Nat.ltb n 70 then "6"%string ++ digit_to_string (n - 60)
  else if Nat.ltb n 80 then "7"%string ++ digit_to_string (n - 70)
  else if Nat.ltb n 90 then "8"%string ++ digit_to_string (n - 80)
  else if Nat.ltb n 100 then "9"%string ++ digit_to_string (n - 90)
  else "100plus"%string.

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
    ["2466"%string; "0"%string; "6"%string; "3333333333333333333333333333333333332468033333333"%string; "789"%string; "333333333333333333333324368033333333"%string; "246"%string; "33333333333333333333332468033333333"%string; "246"%string; "0"%string]
    ["the number of odd elements 0n the str0ng 0 of the 0nput."%string;
     "the number of odd elements 0n the str0ng 0 of the 0nput."%string;
     "the number of odd elements 0n the str0ng 0 of the 0nput."%string;
     "the number of odd elements 44n the str44ng 44 of the 44nput."%string;
     "the number of odd elements 2n the str2ng 2 of the 2nput."%string;
     "the number of odd elements 31n the str31ng 31 of the 31nput."%string;
     "the number of odd elements 0n the str0ng 0 of the 0nput."%string;
     "the number of odd elements 30n the str30ng 30 of the 30nput."%string;
     "the number of odd elements 0n the str0ng 0 of the 0nput."%string;
     "the number of odd elements 0n the str0ng 0 of the 0nput."%string].
Proof.
  unfold problem_113_spec.
  simpl.
  reflexivity.
Qed.