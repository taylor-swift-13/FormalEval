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

Definition digit_ascii (d : nat) : ascii :=
  match d with
  | 0 => "0"%char
  | 1 => "1"%char
  | 2 => "2"%char
  | 3 => "3"%char
  | 4 => "4"%char
  | 5 => "5"%char
  | 6 => "6"%char
  | 7 => "7"%char
  | 8 => "8"%char
  | 9 => "9"%char
  | _ => "?"%char
  end.

Fixpoint inc_digits_rev (ds : list nat) : list nat :=
  match ds with
  | [] => [1]
  | d :: ds' =>
      if Nat.ltb d 9 then (S d) :: ds' else 0 :: inc_digits_rev ds'
  end.

Fixpoint nat_to_digits_rev (n : nat) (ds : list nat) : list nat :=
  match n with
  | 0 => ds
  | S n' => nat_to_digits_rev n' (inc_digits_rev ds)
  end.

Fixpoint string_of_digits (ds : list nat) : string :=
  match ds with
  | [] => EmptyString
  | d :: ds' => String (digit_ascii d) (string_of_digits ds')
  end.

Definition nat_to_string (n : nat) : string :=
  let ds_rev := nat_to_digits_rev n [0] in
  let ds := rev ds_rev in
  string_of_digits ds.

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
     "3333333333333333333333333333333"%string;
     "1111111111111111111111111"%string;
     "3333333333333333333332468033300000000133333"%string;
     "000000000000000"%string;
     "33333333333333333333333333333"%string;
     "3333333333333333333332468033333333"%string;
     "333333333333333333333333333333"%string;
     "33333333333333333333333333333"%string]
    ["the number of odd elements 25n the str25ng 25 of the 25nput."%string;
     "the number of odd elements 31n the str31ng 31 of the 31nput."%string;
     "the number of odd elements 25n the str25ng 25 of the 25nput."%string;
     "the number of odd elements 30n the str30ng 30 of the 30nput."%string;
     "the number of odd elements 0n the str0ng 0 of the 0nput."%string;
     "the number of odd elements 29n the str29ng 29 of the 29nput."%string;
     "the number of odd elements 29n the str29ng 29 of the 29nput."%string;
     "the number of odd elements 30n the str30ng 30 of the 30nput."%string;
     "the number of odd elements 29n the str29ng 29 of the 29nput."%string].
Proof.
  unfold problem_113_spec.
  simpl.
  reflexivity.
Qed.