Require Import Coq.Strings.String Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Arith.
Import ListNotations.
Open Scope string_scope.

Definition is_vowel (c : ascii) : bool :=
  match c with
  | "a"%char | "e"%char | "i"%char | "o"%char | "u"%char => true
  | "A"%char | "E"%char | "I"%char | "O"%char | "U"%char => true
  | _ => false
  end.

Definition swap_case (c : ascii) : ascii :=
  let n := nat_of_ascii c in
  if andb (leb 65 n) (leb n 90)
  then ascii_of_nat (n + 32)
  else if andb (leb 97 n) (leb n 122)
  then ascii_of_nat (n - 32)
  else c.

Definition replace_vowel (c : ascii) : ascii :=
  match c with
  | "a"%char => "c"%char | "e"%char => "g"%char | "i"%char => "k"%char | "o"%char => "q"%char | "u"%char => "w"%char
  | "A"%char => "C"%char | "E"%char => "G"%char | "I"%char => "K"%char | "O"%char => "Q"%char | "U"%char => "W"%char
  | _ => c
  end.

Definition encode_char_spec (c_in c_out : ascii) : Prop :=
  let c_swapped := swap_case c_in in
  if is_vowel c_in
  then c_out = replace_vowel c_swapped
  else c_out = c_swapped.

Definition problem_93_pre (s_in : string) : Prop :=
  let l_in := list_ascii_of_string s_in in
  Forall (fun c => let n := nat_of_ascii c in (65 <= n /\ n <= 90) \/ (97 <= n /\ n <= 122) \/ n = 32) l_in.

Definition problem_93_spec (s_in s_out : string) : Prop :=
  let l_in := list_ascii_of_string s_in in
  let l_out := list_ascii_of_string s_out in
  Forall2 encode_char_spec l_in l_out.

Example test_encode_long : problem_93_spec "ABCDThe cat in tabcdefghijklmn opqrstuvwxABCDThe rcat in tabcdefghijklmnopqrstuvwxyzhe hatFyzhe hatF" "cbcdtHG CCT KN TCBCDGFGHKJKLMN QPQRSTWVWXcbcdtHG RCCT KN TCBCDGFGHKJKLMNQPQRSTWVWXYZHG HCTfYZHG HCTf".
Proof.
  unfold problem_93_spec.
  simpl.
  unfold encode_char_spec.
  repeat constructor.
Qed.