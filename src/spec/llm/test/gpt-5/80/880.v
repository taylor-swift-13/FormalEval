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

Lemma nth_error_string_Some_length: forall s n a, nth_error_string s n = Some a -> n < String.length s.
Proof.
  induction s as [|ch s' IH]; intros n a H; simpl in *.
  - discriminate.
  - destruct n as [|n'].
    + inversion H; subst; simpl; lia.
    + apply IH in H. simpl. lia.
Qed.

Example test_is_happy_long:
  is_happy_spec
    ("abcdeaaaaabbbbccababa112233445abcdeaaaaabbbbccababa1122334455667788990011223344556677889900112a2334455667abcabcabcabbcabcabcabcabcabcabcabaaddbbcaaaaabbbbccccdddda1111223344aaddbbccddeeaabbcacaaaaaabbbbccccddddaaaabbbbcccccddcddbabcccaaabbd112233445566077889900112233aaddbbccddeeaabbccddee45566778899001122334455667abcabcabcabcabcabcabc9900deefffccccddddddee5566772334459002233445566778899001122334455667788990011223344556677889900aaabbbbccccddddaaaabbbbccccdddddbababababccdeeeddddccccbbbbaaaaeeeedddccccafghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyz"%string)
    false.
Proof.
  set (s := "abcdeaaaaabbbbccababa112233445abcdeaaaaabbbbccababa1122334455667788990011223344556677889900112a2334455667abcabcabcabbcabcabcabcabcabcabcabaaddbbcaaaaabbbbccccdddda1111223344aaddbbccddeeaabbcacaaaaaabbbbccccddddaaaabbbbcccccddcddbabcccaaabbd112233445566077889900112233aaddbbccddeeaabbccddee45566778899001122334455667abcabcabcabcabcabcabc9900deefffccccddddddee5566772334459002233445566778899001122334455667788990011223344556677889900aaabbbbccccddddaaaabbbbccccdddddbababababccdeeeddddccccbbbbaaaaeeeedddccccafghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyz"%string) in *.
  right.
  split.
  - reflexivity.
  - unfold not; intros H.
    unfold happy_prop in H.
    destruct H as [Hlen Hall].
    assert (Hex8: exists a0, nth_error_string s 8 = Some a0) by (unfold s; simpl; eexists; reflexivity).
    destruct Hex8 as [a8 Ha8].
    apply nth_error_string_Some_length in Ha8.
    specialize (Hall 6).
    assert (6 + 2 < String.length s) by lia.
    specialize (Hall H).
    destruct Hall as [a [b [c [Ha [Hb [Hc Hdist]]]]]].
    unfold s in Ha, Hb; simpl in Ha, Hb.
    inversion Ha; subst.
    inversion Hb; subst.
    destruct Hdist as [Hab _].
    apply Hab. reflexivity.
Qed.