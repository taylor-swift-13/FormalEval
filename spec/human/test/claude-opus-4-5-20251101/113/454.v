Require Import Coq.Strings.String Coq.Lists.List Coq.Strings.Ascii Coq.Arith.PeanoNat.
Import ListNotations.

Definition is_odd_digit (c : ascii) : bool :=
  match c with "1"%char|"3"%char|"5"%char|"7"%char|"9"%char => true | _ => false end.

Fixpoint count_odd_digits (s : string) : nat :=
  match s with EmptyString => 0 | String c s' => (if is_odd_digit c then 1 else 0) + count_odd_digits s' end.

Definition digit_to_char (n : nat) : ascii := ascii_of_nat (48 + (n mod 10)).

Fixpoint nat_to_string_aux (fuel : nat) (n : nat) : string :=
  match fuel with
  | 0 => EmptyString
  | S fuel' =>
    match n with
    | 0 => EmptyString
    | _ => String (digit_to_char n) (nat_to_string_aux fuel' (n / 10))
    end
  end.

Fixpoint rev_string (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => (rev_string s') ++ String c EmptyString
  end.

Definition nat_to_string (n : nat) : string :=
  match n with
  | 0 => "0"%string
  | _ => rev_string (nat_to_string_aux n n)
  end.

Fixpoint replace_char_with_string (target : ascii) (replacement : string) (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => let rest := replace_char_with_string target replacement s' in
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

Example test_odd_count :
  problem_113_spec ["0"%string; "2"%string; "99991010333333333333331010111111199935799999999999"%string; "6"%string; "8"%string; "000"%string; "22"%string; "352468901357945679"%string; "8"%string; "0"%string]
                   ["the number of odd elements 0n the str0ng 0 of the 0nput."%string;
                    "the number of odd elements 0n the str0ng 0 of the 0nput."%string;
                    "the number of odd elements 46n the str46ng 46 of the 46nput."%string;
                    "the number of odd elements 0n the str0ng 0 of the 0nput."%string;
                    "the number of odd elements 0n the str0ng 0 of the 0nput."%string;
                    "the number of odd elements 0n the str0ng 0 of the 0nput."%string;
                    "the number of odd elements 0n the str0ng 0 of the 0nput."%string;
                    "the number of odd elements 11n the str11ng 11 of the 11nput."%string;
                    "the number of odd elements 0n the str0ng 0 of the 0nput."%string;
                    "the number of odd elements 0n the str0ng 0 of the 0nput."%string].
Proof.
  unfold problem_113_spec, odd_count_impl, process_string.
  simpl.
  reflexivity.
Qed.