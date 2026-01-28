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

Definition ascii_of_digit (d : nat) : ascii := ascii_of_nat (48 + d).

Fixpoint nat_to_string_aux (k n : nat) : string :=
  match k with
  | 0 => "0"%string
  | S k' =>
      if Nat.ltb n 10
      then String (ascii_of_digit n) EmptyString
      else nat_to_string_aux k' (Nat.div n 10) ++ String (ascii_of_digit (Nat.modulo n 10)) EmptyString
  end.

Definition nat_to_string (n : nat) : string := nat_to_string_aux (S n) n.

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
     "999999999999911111111999999999999"%string;
     "11111111111111111111"%string;
     "99999999999999"%string;
     "33333333333333333333333333333"%string]
    ["the number of odd elements 25n the str25ng 25 of the 25nput."%string;
     "the number of odd elements 33n the str33ng 33 of the 33nput."%string;
     "the number of odd elements 20n the str20ng 20 of the 20nput."%string;
     "the number of odd elements 14n the str14ng 14 of the 14nput."%string;
     "the number of odd elements 29n the str29ng 29 of the 29nput."%string].
Proof.
  unfold problem_113_spec.
  simpl.
  reflexivity.
Qed.