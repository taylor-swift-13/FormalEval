Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Arith.
Import ListNotations.
Open Scope string_scope.

Definition is_lower (c : ascii) : bool :=
  let n := nat_of_ascii c in
  andb (Nat.leb 97 n) (Nat.leb n 122).

Definition decode_char (c : ascii) : ascii :=
  let n := nat_of_ascii c in
  if is_lower c then
    let a := nat_of_ascii "a"%char in
    ascii_of_nat (a + (n - a + 21) mod 26)
  else
    c.

Definition problem_50_pre (l' : string) : Prop := True.

Definition problem_50_spec (l' l : string) : Prop :=
  let list_l := list_ascii_of_string l in
  let list_l' := list_ascii_of_string l' in
  list_l = map decode_char list_l'.

Fixpoint decode_string (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c rest => String (decode_char c) (decode_string rest)
  end.

Lemma decode_string_correct : forall s,
  list_ascii_of_string (decode_string s) = map decode_char (list_ascii_of_string s).
Proof.
  induction s.
  - simpl. reflexivity.
  - simpl. rewrite IHs. reflexivity.
Qed.

Example test_decode_shift :
  problem_50_spec "worello abcdew orl dld" "rjmzggj vwxyzr jmg ygy".
Proof.
  unfold problem_50_spec.
  simpl.
  unfold decode_char.
  simpl.
  reflexivity.
Qed.