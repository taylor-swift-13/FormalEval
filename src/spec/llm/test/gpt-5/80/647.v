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
    ("qwertyuiopasdfghjklzxcvbnmqwaaaaabbbbccababa1122334455667788990011223344556677889900112a2334455667abcabcabcabcabcabcabcabcabcabcabaaddbbccddeeaabbccddeebcab7889900babababababababababababababababababababababccdeeeddddccabcdefgabcdefgc112233445566077889900112233445566778899001122334455667abcabcabcabcabcabcabcabcabcabcabaadbbccddeeaabbccddeebcab7889900abcdefgcdefefgyuiopasdfghjklzxcvb"%string)
    false.
Proof.
  right.
  split.
  - reflexivity.
  - unfold not; intros H.
    remember ("qwertyuiopasdfghjklzxcvbnmqwaaaaabbbbccababa1122334455667788990011223344556677889900112a2334455667abcabcabcabcabcabcabcabcabcabcabaaddbbccddeeaabbccddeebcab7889900babababababababababababababababababababababccdeeeddddccabcdefgabcdefgc112233445566077889900112233445566778899001122334455667abcabcabcabcabcabcabcabcabcabcabaadbbccddeeaabbccddeebcab7889900abcdefgcdefefgyuiopasdfghjklzxcvb"%string) as s eqn:Hs.
    unfold happy_prop in H.
    destruct H as [Hlen Hall].
    assert (28 + 2 < String.length s).
    { rewrite Hs. simpl. lia. }
    specialize (Hall 28 H).
    destruct Hall as [a [b [c [Ha [Hb [Hc Hd]]]]]].
    rewrite Hs in Hb.
    rewrite Hs in Hc.
    simpl in Hb.
    simpl in Hc.
    inversion Hb; subst b.
    inversion Hc; subst c.
    destruct Hd as [_ [_ Hbc]].
    apply Hbc.
    reflexivity.
Qed.