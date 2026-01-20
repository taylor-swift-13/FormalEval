Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Lia.

Fixpoint nth_error_string (s : string) (n : nat) : option ascii :=
  match s, n with
  | EmptyString, _ => None
  | String a s', 0 => Some a
  | String _ s', S n' => nth_error_string s' n'
  end.

Definition distinct3 (a b c : ascii) : Prop :=
  a <> b /\ a <> c /\ b <> c.

Definition happy_prop (s : string) : Prop :=
  3 <= String.length s /\
  forall i, i + 2 < String.length s ->
    exists a b c,
      nth_error_string s i = Some a /\
      nth_error_string s (i + 1) = Some b /\
      nth_error_string s (i + 2) = Some c /\
      distinct3 a b c.

Definition is_happy_spec (s : string) (r : bool) : Prop :=
  (r = true /\ happy_prop s) \/ (r = false /\ ~ happy_prop s).

Example test_is_happy_long: is_happy_spec ("112233445566077889900112233445566778899001122334455667abcabcabcabcabcabcabcab3cabcabcabaadbbccddeeaabbccddeebcab7889900"%string) false.
Proof.
  right.
  split.
  - reflexivity.
  - intros Hh.
    unfold happy_prop in Hh.
    destruct Hh as [Hlen Hall].
    specialize (Hall 0).
    assert (Hcond: 0 + 2 < String.length ("112233445566077889900112233445566778899001122334455667abcabcabcabcabcabcabcab3cabcabcabaadbbccddeeaabbccddeebcab7889900"%string)) by lia.
    specialize (Hall Hcond).
    destruct Hall as [x [y [z [Hx [Hy [Hz Hdist]]]]]].
    simpl in Hx.
    simpl in Hy.
    inversion Hx; subst.
    inversion Hy; subst.
    destruct Hdist as [Hxy _].
    apply Hxy.
    reflexivity.
Qed.