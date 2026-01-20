Require Import Coq.Strings.String Coq.Lists.List Coq.Strings.Ascii Coq.Arith.PeanoNat.
Import ListNotations.

Definition is_odd_digit (c : ascii) : bool :=
  match c with "1"%char|"3"%char|"5"%char|"7"%char|"9"%char => true | _ => false end.

Fixpoint count_odd_digits (s : string) : nat :=
  match s with EmptyString => 0 | String c s' => (if is_odd_digit c then 1 else 0) + count_odd_digits s' end.

Definition nat_to_digit_char (n : nat) : ascii :=
  match n with 0=>"0"%char|1=>"1"%char|2=>"2"%char|3=>"3"%char|4=>"4"%char|5=>"5"%char|6=>"6"%char|7=>"7"%char|8=>"8"%char|_=>"9"%char end.

Fixpoint replace_char (target replacement : ascii) (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => let rest := replace_char target replacement s' in
                   let cur := if Ascii.eqb c target then replacement else c in
                   String cur rest
  end.

Definition process_string (s : string) : string :=
  let cnt := count_odd_digits s in
  let ch := nat_to_digit_char cnt in
  let templ := "the number of odd elements in the string i of the input."%string in
  replace_char "i"%char ch templ.

Definition odd_count_impl (input : list string) : list string := map process_string input.

Example odd_count_impl_ex:
  odd_count_impl ("123"%string :: nil) =
  ("the number of odd elements 2n the str2ng 2 of the 2nput."%string :: nil).
Proof. reflexivity. Qed.

Example odd_count_impl_two:
  odd_count_impl ("3"%string :: "11111111"%string :: nil) =
  ("the number of odd elements 1n the str1ng 1 of the 1nput."%string ::
   "the number of odd elements 8n the str8ng 8 of the 8nput."%string :: nil).
Proof. reflexivity. Qed.

Definition odd_count_spec (input : list string) (output : list string) : Prop :=
  output = odd_count_impl input.


