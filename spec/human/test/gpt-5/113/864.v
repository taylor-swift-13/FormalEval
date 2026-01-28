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

Definition digit_to_char (d : nat) : ascii :=
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
  | _ => "0"%char
  end.

Fixpoint divmod10 (n fuel : nat) : nat * nat :=
  match fuel with
  | 0 => (0, n)
  | S fuel' =>
      if Nat.ltb n 10 then (0, n)
      else let '(q, r) := divmod10 (n - 10) fuel' in (S q, r)
  end.

Fixpoint nat_to_string_rec (n fuel : nat) : string :=
  match fuel with
  | 0 => "0"%string
  | S fuel' =>
      if Nat.ltb n 10 then String (digit_to_char n) EmptyString
      else let '(q, r) := divmod10 n fuel' in
           nat_to_string_rec q fuel' ++ String (digit_to_char r) EmptyString
  end.

Definition nat_to_string (n : nat) : string := nat_to_string_rec n n.

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

Fixpoint all_digits (t : string) : Prop :=
  match t with
  | EmptyString => True
  | String ch rest =>
      let n := nat_of_ascii ch in (48 <= n /\ n <= 57) /\ all_digits rest
  end.

Definition problem_113_pre (input : list string) : Prop :=
  Forall (fun s => all_digits s) input.

Definition problem_113_spec (input : list string) (output : list string) : Prop :=
  output = odd_count_impl input.

Example odd_count_test_case_1 :
  problem_113_spec
    ["2466"%string; "789"%string; "246"%string; "2805555555555555555555555552"%string; "2802"%string; "246"%string; "333333333333333"%string]
    ["the number of odd elements 0n the str0ng 0 of the 0nput."%string;
     "the number of odd elements 2n the str2ng 2 of the 2nput."%string;
     "the number of odd elements 0n the str0ng 0 of the 0nput."%string;
     "the number of odd elements 24n the str24ng 24 of the 24nput."%string;
     "the number of odd elements 0n the str0ng 0 of the 0nput."%string;
     "the number of odd elements 0n the str0ng 0 of the 0nput."%string;
     "the number of odd elements 15n the str15ng 15 of the 15nput."%string].
Proof.
  unfold problem_113_spec.
  vm_compute.
  reflexivity.
Qed.