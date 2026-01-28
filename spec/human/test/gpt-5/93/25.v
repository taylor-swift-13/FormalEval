Require Import Coq.Strings.String Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Arith.
Require Import Lia.
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

Definition encode_char (c : ascii) : ascii :=
  let c_swapped := swap_case c in
  if is_vowel c
  then replace_vowel c_swapped
  else c_swapped.

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

Lemma encode_char_spec_refl : forall c, encode_char_spec c (encode_char c).
Proof.
  intros. unfold encode_char_spec, encode_char. destruct (is_vowel c); reflexivity.
Qed.

Lemma Forall2_encode_map : forall l, Forall2 encode_char_spec l (map encode_char l).
Proof.
  induction l; simpl; constructor; auto using encode_char_spec_refl.
Qed.

Example test_problem_93_new :
  problem_93_pre "to be or notZYXWVUTSRQPONMLKJIABCDEFHGFEDCBA to be" /\
  problem_93_spec "to be or notZYXWVUTSRQPONMLKJIABCDEFHGFEDCBA to be" "TQ BG QR NQTzyxwvwtsrqpqnmlkjkcbcdgfhgfgdcbc TQ BG".
Proof.
  split.
  - unfold problem_93_pre.
    simpl.
    repeat match goal with
    | |- Forall _ (_ :: _) => constructor
    | |- Forall _ [] => constructor
    | |- _ \/ _ \/ _ =>
        (left; split; vm_compute; lia) ||
        (right; left; split; vm_compute; lia) ||
        (right; right; vm_compute; reflexivity)
    end.
  - unfold problem_93_spec.
    simpl.
    replace (list_ascii_of_string "TQ BG QR NQTzyxwvwtsrqpqnmlkjkcbcdgfhgfgdcbc TQ BG")
      with (map encode_char (list_ascii_of_string "to be or notZYXWVUTSRQPONMLKJIABCDEFHGFEDCBA to be")).
    + apply Forall2_encode_map.
    + vm_compute. reflexivity.
Qed.