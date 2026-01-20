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

Example test_is_happy_long:
  is_happy_spec
    ("abcabcabcabcacabcabcabcabcacbcabc8abcabcabcabcaabcccaaabbd112233445566077889900112233445566778899001122334455667abcabcabcabcabcabcabcabcabcabcabaaddbbccddeeaabbccddeebcab7889900deefffbcabcabcabcabcabcab55667abcabcabcabcabcabcabcabcabcaaaaaabbbbccccddddaaaabbbbccccddddaaaabbbbccccdddddbcabaaddbbccddeeaabbccddeebcab7889900deefffbcabcabcabcabcabcab"%string)
    false.
Proof.
  right.
  split.
  - reflexivity.
  - unfold not; intros H.
    unfold happy_prop in H.
    destruct H as [Hlen Hall].
    assert (Hlt: 11 + 2 < String.length
      ("abcabcabcabcacabcabcabcabcacbcabc8abcabcabcabcaabcccaaabbd112233445566077889900112233445566778899001122334455667abcabcabcabcabcabcabcabcabcabcabaaddbbccddeeaabbccddeebcab7889900deefffbcabcabcabcabcabcab55667abcabcabcabcabcabcabcabcabcaaaaaabbbbccccddddaaaabbbbccccddddaaaabbbbccccdddddbcabaaddbbccddeeaabbccddeebcab7889900deefffbcabcabcabcabcabcab"%string))
      by (simpl; lia).
    pose proof (Hall 11 Hlt) as Halli.
    destruct Halli as [a [b [c [H1 [H2 [H3 Hd]]]]]].
    simpl in H1, H2, H3.
    inversion H1; subst.
    inversion H3; subst.
    destruct Hd as [Hab [Hac Hbc]].
    apply Hac.
    reflexivity.
Qed.