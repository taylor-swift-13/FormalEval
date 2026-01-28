Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Arith.
Import ListNotations.
Open Scope string_scope.

Definition decode_char (c : ascii) : ascii :=
  let n := nat_of_ascii c in
  let a := nat_of_ascii "a"%char in
  ascii_of_nat (a + (n - a + 21) mod 26).

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

Lemma ascii_of_nat_98 : ascii_of_nat 98 = "b"%char.
Proof. reflexivity. Qed.

Lemma ascii_of_nat_103 : ascii_of_nat 103 = "g"%char.
Proof. reflexivity. Qed.

Lemma ascii_of_nat_113 : ascii_of_nat 113 = "q"%char.
Proof. reflexivity. Qed.

Lemma ascii_of_nat_117 : ascii_of_nat 117 = "u"%char.
Proof. reflexivity. Qed.

Lemma ascii_of_nat_106 : ascii_of_nat 106 = "j"%char.
Proof. reflexivity. Qed.

Example test_decode_shift :
  problem_50_spec "glvzp" "bgquj".
Proof.
  unfold problem_50_spec.
  simpl.
  unfold decode_char.
  simpl.
  reflexivity.
Qed.