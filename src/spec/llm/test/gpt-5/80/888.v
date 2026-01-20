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

Lemma String_length_append : forall s1 s2,
  String.length (String.append s1 s2) = String.length s1 + String.length s2.
Proof.
  intros s1 s2.
  induction s1.
  - simpl. reflexivity.
  - simpl. rewrite IHs1. reflexivity.
Qed.

Lemma nth_error_string_append_right :
  forall s1 s2 n,
    String.length s1 <= n ->
    nth_error_string (String.append s1 s2) n =
    nth_error_string s2 (n - String.length s1).
Proof.
  intros s1 s2 n Hle.
  revert n Hle.
  induction s1 as [|a s1' IH]; intros n Hle.
  - simpl. now rewrite Nat.sub_0_r.
  - simpl in *.
    destruct n.
    + lia.
    + simpl.
      apply IH.
      lia.
Qed.

Example test_is_happy_long: is_happy_spec ("qwertyuiopasdefghjklzxcvbnmq11223344556677889900112bcabcabaaddbbccddeeaabbccddeebcab7889900wertqwertyuiopasdefghjklzxcvbnmqwertyuiopasabocccaaabbdd11223344556677889900112233445566778899001122334455667abcabcaabcabcabcabcacbcabc8abcabcabcabcaabcccaaabbd112233445566077889900112233445566778899001122334455667abcabcabcabcabcabcabcabcabcabcabaaddbbccddeeaabbccddeebcab7889900deefffbcabcabcabcabcabca1bb4cabcabcabcabcabcabcabcabaaddbbccddeeaabbccddeebcab7889900deefffdfghjklzxcvbjklzxcvb"%string) false.
Proof.
  right.
  split.
  - reflexivity.
  - unfold not; intros H.
    unfold happy_prop in H.
    destruct H as [Hlen Hall].
    set (prefix := "qwertyuiopasdefghjklzxcvbnmq"%string).
    set (tail := "11223344556677889900112bcabcabaaddbbccddeeaabbccddeebcab7889900wertqwertyuiopasdefghjklzxcvbnmqwertyuiopasabocccaaabbdd11223344556677889900112233445566778899001122334455667abcabcaabcabcabcabcacbcabc8abcabcabcabcaabcccaaabbd112233445566077889900112233445566778899001122334455667abcabcabcabcabcabcabcabcabcabcabaaddbbccddeeaabbccddeebcab7889900deefffbcabcabcabcabcabca1bb4cabcabcabcabcabcabcabcabaaddbbccddeeaabbccddeebcab7889900deefffdfghjklzxcvbjklzxcvb"%string).
    replace ("qwertyuiopasdefghjklzxcvbnmq11223344556677889900112bcabcabaaddbbccddeeaabbccddeebcab7889900wertqwertyuiopasdefghjklzxcvbnmqwertyuiopasabocccaaabbdd11223344556677889900112233445566778899001122334455667abcabcaabcabcabcabcacbcabc8abcabcabcabcaabcccaaabbd112233445566077889900112233445566778899001122334455667abcabcabcabcabcabcabcabcabcabcabaaddbbccddeeaabbccddeebcab7889900deefffbcabcabcabcabcabca1bb4cabcabcabcabcabcabcabcabaaddbbccddeeaabbccddeebcab7889900deefffdfghjklzxcvbjklzxcvb"%string)
      with (String.append prefix tail) in * by reflexivity.
    assert (Cond: String.length prefix + 2 < String.length (String.append prefix tail)).
    {
      rewrite String_length_append.
      simpl.
      lia.
    }
    specialize (Hall (String.length prefix)).
    specialize (Hall Cond).
    destruct Hall as [a [b [c [Ha [Hb [Hc Hdist]]]]]].
    assert (Eeq:
      nth_error_string (String.append prefix tail) (String.length prefix) =
      nth_error_string (String.append prefix tail) (String.length prefix + 1)).
    {
      rewrite nth_error_string_append_right with (s1:=prefix) (s2:=tail) (n:=String.length prefix); [|lia].
      rewrite nth_error_string_append_right with (s1:=prefix) (s2:=tail) (n:=String.length prefix + 1); [|lia].
      simpl.
      reflexivity.
    }
    rewrite Ha in Eeq.
    rewrite Hb in Eeq.
    inversion Eeq; subst b.
    destruct Hdist as [Hab _].
    apply Hab.
    reflexivity.
Qed.