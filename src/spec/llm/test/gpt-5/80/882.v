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

Lemma nth_error_string_some_lt_length:
  forall s n ch, nth_error_string s n = Some ch -> n < String.length s.
Proof.
  induction s as [|a s' IH]; intros n ch H; simpl in H.
  - destruct n; inversion H.
  - destruct n.
    + inversion H; simpl; lia.
    + specialize (IH n ch H). simpl. lia.
Qed.

Example test_is_happy_long: is_happy_spec ("abcdeaaaaabbbbccababa112233445abcdeaaaaabbbbccababa1122334455667788990011223344556677889900112a2334455667abcabcabcabbcabcabcabcabcabcabcabaaddbbcaaaaabbbbccccdddda1111223344aaddbbccddeeaabbcacaaaaaabbbbccccddddaaaabbbbcccccddcddbabcccaaabbd1122334455660778899d00112233aaddbbccddeeaabbccddee45566778899001122334455667abcabcabcabcabcabcabc9900deefffccccddddddee5566772334459002233445566778899001122334455667788990011223344556677889900aaabbbbccccddddaaaabbbbccccdddddbababababccdeeeddddccccbbbbaaaaeeeedddccccafghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyz"%string) false.
Proof.
  right.
  split.
  - reflexivity.
  - intros H.
    unfold happy_prop in H.
    destruct H as [Hlen Hall].
    assert (Hlen7: 7 < String.length ("abcdeaaaaabbbbccababa112233445abcdeaaaaabbbbccababa1122334455667788990011223344556677889900112a2334455667abcabcabcabbcabcabcabcabcabcabcabaaddbbcaaaaabbbbccccdddda1111223344aaddbbccddeeaabbcacaaaaaabbbbccccddddaaaabbbbcccccddcddbabcccaaabbd1122334455660778899d00112233aaddbbccddeeaabbccddee45566778899001122334455667abcabcabcabcabcabcabc9900deefffccccddddddee5566772334459002233445566778899001122334455667788990011223344556677889900aaabbbbccccddddaaaabbbbccccdddddbababababccdeeeddddccccbbbbaaaaeeeedddccccafghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyz"%string)).
    { assert (H7: nth_error_string ("abcdeaaaaabbbbccababa112233445abcdeaaaaabbbbccababa1122334455667788990011223344556677889900112a2334455667abcabcabcabbcabcabcabcabcabcabcabaaddbbcaaaaabbbbccccdddda1111223344aaddbbccddeeaabbcacaaaaaabbbbccccddddaaaabbbbcccccddcddbabcccaaabbd1122334455660778899d00112233aaddbbccddeeaabbccddee45566778899001122334455667abcabcabcabcabcabcabc9900deefffccccddddddee5566772334459002233445566778899001122334455667788990011223344556677889900aaabbbbccccddddaaaabbbbccccdddddbababababccdeeeddddccccbbbbaaaaeeeedddccccafghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyz"%string) 7 = Some "a"%char) by (simpl; reflexivity).
      eapply nth_error_string_some_lt_length in H7.
      exact H7.
    }
    specialize (Hall 5).
    specialize (Hall Hlen7).
    destruct Hall as [a [b [c [Ha [Hb [Hc Hdist]]]]]].
    simpl in Ha. inversion Ha. subst a.
    simpl in Hb. inversion Hb. subst b.
    simpl in Hc. inversion Hc. subst c.
    destruct Hdist as [Hab _].
    apply Hab. reflexivity.
Qed.