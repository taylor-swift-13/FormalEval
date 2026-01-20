Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.

Fixpoint InStr (a : ascii) (s : string) : Prop :=
  match s with
  | EmptyString => False
  | String b s' => a = b \/ InStr a s'
  end.

Definition same_char_sets (s0 s1 : string) : Prop :=
  forall a : ascii, InStr a s0 <-> InStr a s1.

Definition same_chars_spec (s0 s1 : string) (res : bool) : Prop :=
  (res = true <-> same_char_sets s0 s1) /\
  (res = false <-> ~ same_char_sets s0 s1).

(* Helper lemma for ascii equality decidability *)
Lemma ascii_dec : forall a b : ascii, {a = b} + {a <> b}.
Proof.
  intros a b.
  destruct a as [a0 a1 a2 a3 a4 a5 a6 a7].
  destruct b as [b0 b1 b2 b3 b4 b5 b6 b7].
  destruct a0; destruct b0; try (right; intro H; inversion H; fail);
  destruct a1; destruct b1; try (right; intro H; inversion H; fail);
  destruct a2; destruct b2; try (right; intro H; inversion H; fail);
  destruct a3; destruct b3; try (right; intro H; inversion H; fail);
  destruct a4; destruct b4; try (right; intro H; inversion H; fail);
  destruct a5; destruct b5; try (right; intro H; inversion H; fail);
  destruct a6; destruct b6; try (right; intro H; inversion H; fail);
  destruct a7; destruct b7; try (right; intro H; inversion H; fail);
  left; reflexivity.
Qed.

(* Define the strings *)
Definition s0 : string := "eabcdzzzz".
Definition s1 : string := "dddzzzzzzzddeddabc".

(* The characters in s0 are: e, a, b, c, d, z *)
(* The characters in s1 are: d, z, e, a, b, c *)
(* So they have the same character sets *)

Lemma InStr_s0 : forall a, InStr a s0 <-> 
  (a = "e"%char \/ a = "a"%char \/ a = "b"%char \/ a = "c"%char \/ a = "d"%char \/ a = "z"%char).
Proof.
  intro a.
  unfold s0.
  simpl.
  split; intro H.
  - destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]];
    try (left; exact H); try (right; left; exact H);
    try (right; right; left; exact H); try (right; right; right; left; exact H);
    try (right; right; right; right; left; exact H);
    try (right; right; right; right; right; exact H);
    try contradiction.
  - destruct H as [H|[H|[H|[H|[H|H]]]]];
    try (left; exact H);
    try (right; left; exact H);
    try (right; right; left; exact H);
    try (right; right; right; left; exact H);
    try (right; right; right; right; left; exact H);
    try (right; right; right; right; right; left; exact H);
    try (right; right; right; right; right; right; left; exact H);
    try (right; right; right; right; right; right; right; left; exact H);
    try (right; right; right; right; right; right; right; right; left; exact H);
    try (right; right; right; right; right; right; right; right; right; exact H).
Qed.

Lemma InStr_s1 : forall a, InStr a s1 <-> 
  (a = "d"%char \/ a = "z"%char \/ a = "e"%char \/ a = "a"%char \/ a = "b"%char \/ a = "c"%char).
Proof.
  intro a.
  unfold s1.
  simpl.
  split; intro H.
  - destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]]]]]]]];
    try (left; exact H);
    try (right; left; exact H);
    try (right; right; left; exact H);
    try (right; right; right; left; exact H);
    try (right; right; right; right; left; exact H);
    try (right; right; right; right; right; exact H);
    try contradiction.
  - destruct H as [H|[H|[H|[H|[H|H]]]]];
    subst;
    try (left; reflexivity);
    try (right; left; reflexivity);
    try (right; right; left; reflexivity);
    try (right; right; right; left; reflexivity);
    try (right; right; right; right; left; reflexivity);
    try (right; right; right; right; right; left; reflexivity);
    try (right; right; right; right; right; right; left; reflexivity);
    try (right; right; right; right; right; right; right; left; reflexivity);
    try (right; right; right; right; right; right; right; right; left; reflexivity);
    try (right; right; right; right; right; right; right; right; right; left; reflexivity);
    try (right; right; right; right; right; right; right; right; right; right; left; reflexivity);
    try (right; right; right; right; right; right; right; right; right; right; right; left; reflexivity);
    try (right; right; right; right; right; right; right; right; right; right; right; right; left; reflexivity);
    try (right; right; right; right; right; right; right; right; right; right; right; right; right; left; reflexivity);
    try (right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; reflexivity);
    try (right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; reflexivity);
    try (right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; reflexivity);
    try (right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; reflexivity);
    try (right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; reflexivity).
Qed.

Lemma same_char_sets_s0_s1 : same_char_sets s0 s1.
Proof.
  unfold same_char_sets.
  intro a.
  rewrite InStr_s0, InStr_s1.
  split; intro H.
  - destruct H as [H|[H|[H|[H|[H|H]]]]]; subst;
    try (right; right; left; reflexivity);
    try (right; right; right; left; reflexivity);
    try (right; right; right; right; left; reflexivity);
    try (right; right; right; right; right; reflexivity);
    try (left; reflexivity);
    try (right; left; reflexivity).
  - destruct H as [H|[H|[H|[H|[H|H]]]]]; subst;
    try (right; right; right; right; left; reflexivity);
    try (right; right; right; right; right; reflexivity);
    try (left; reflexivity);
    try (right; left; reflexivity);
    try (right; right; left; reflexivity);
    try (right; right; right; left; reflexivity).
Qed.

Example test_same_chars : same_chars_spec s0 s1 true.
Proof.
  unfold same_chars_spec.
  split.
  - split.
    + intro. exact same_char_sets_s0_s1.
    + intro. reflexivity.
  - split.
    + intro H. discriminate H.
    + intro H. exfalso. apply H. exact same_char_sets_s0_s1.
Qed.