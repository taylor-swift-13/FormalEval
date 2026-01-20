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

Lemma nth_error_string_Some_lt_length :
  forall s n a, nth_error_string s n = Some a -> n < String.length s.
Proof.
  induction s as [| ch s' IH]; intros n a H; simpl in *.
  - discriminate.
  - destruct n as [| n']; simpl in *.
    + inversion H; subst; lia.
    + apply IH in H. simpl. lia.
Qed.

Example test_is_happy_long: is_happy_spec ("abcbcabcaaaaabbbbccccdeeeddddccccbbbbaaaaeeaaccccddddaaaabbbbccccddddaaaababbbccccddddeedddcabcabcaaaaaabbbbccccddddaaaabbbbccdccddddaaaabbbbccccabababababababaaaaabbbbccccdeeeddddccccbbbbaaaaaaaabbqwertyuiopasdfghjklzxcvbnmqwertyabcabujiopaDJjGkGksdfghjklzxcvbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddccccaabababababababababababababababababdddbcabcabcabaaaaabbbbccccddddaaaabbbbccdccddddaaaabbbbccccababababababababababababababababababababababababdddcabcabcabcabcabcabb"%string) false.
Proof.
  right.
  split.
  - reflexivity.
  - unfold not; intros H.
    unfold happy_prop in H.
    destruct H as [Hlen Hall].
    set (s := "abcbcabcaaaaabbbbccccdeeeddddccccbbbbaaaaeeaaccccddddaaaabbbbccccddddaaaababbbccccddddeedddcabcabcaaaaaabbbbccccddddaaaabbbbccdccddddaaaabbbbccccabababababababaaaaabbbbccccdeeeddddccccbbbbaaaaaaaabbqwertyuiopasdfghjklzxcvbnmqwertyabcabujiopaDJjGkGksdfghjklzxcvbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddccccaabababababababababababababababababdddbcabcabcabaaaaabbbbccccddddaaaabbbbccdccddddaaaabbbbccccababababababababababababababababababababababababdddcabcabcabcabcabcabb"%string).
    assert (H10: nth_error_string s 10 = Some "a"%char) by (unfold s; simpl; reflexivity).
    assert (Hlt: 8 + 2 < String.length s).
    { apply (nth_error_string_Some_lt_length s 10 "a"%char) in H10.
      replace (8 + 2) with 10 by lia.
      exact H10. }
    specialize (Hall 8).
    specialize (Hall Hlt).
    destruct Hall as [a [b [c [Ha [Hb [Hc Hdistinct]]]]]].
    unfold s in Ha, Hb, Hc.
    simpl in Ha, Hb, Hc.
    inversion Ha; subst.
    inversion Hb; subst.
    inversion Hc; subst.
    destruct Hdistinct as [Hab [Hac Hbc]].
    apply Hab. reflexivity.
Qed.