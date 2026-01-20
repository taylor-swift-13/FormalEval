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

Lemma nth_error_string_Some_lt_len:
  forall s n a, nth_error_string s n = Some a -> n < String.length s.
Proof.
  intros s.
  induction s as [|ch s' IH]; intros n a H.
  - simpl in H. discriminate.
  - simpl in *.
    destruct n.
    + inversion H; subst. lia.
    + eapply lt_n_S.
      eapply IH. exact H.
Qed.

Example test_is_happy_long: is_happy_spec
  ("qwertyuiopasdfghjklzxcvbnmwaaaaabbbbccccdeeeddddccccbbbbaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddccccaabcabcabcabcabcabcabcabcadbcabcabcabcaaccccddddaaaabbbbccccddddaaaabbbbccccddddabbcabcabertlyuiopasdfghjkldzxcvb"%string)
  false.
Proof.
  right.
  split.
  - reflexivity.
  - unfold not; intros H.
    unfold happy_prop in H.
    destruct H as [Hlen Hall].
    set (i := 27).
    assert (Hi2 : i + 2 <
      String.length
        ("qwertyuiopasdfghjklzxcvbnmwaaaaabbbbccccdeeeddddccccbbbbaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddccccaabcabcabcabcabcabcabcabcadbcabcabcabcaaccccddddaaaabbbbccccddddaaaabbbbccccddddabbcabcabertlyuiopasdfghjkldzxcvb"%string)).
    {
      assert (Hex: exists ch,
                nth_error_string
                  ("qwertyuiopasdfghjklzxcvbnmwaaaaabbbbccccdeeeddddccccbbbbaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddccccaabcabcabcabcabcabcabcabcadbcabcabcabcaaccccddddaaaabbbbccccddddaaaabbbbccccddddabbcabcabertlyuiopasdfghjkldzxcvb"%string)
                  (i + 2) = Some ch).
      { eexists; reflexivity. }
      destruct Hex as [ch Hch].
      eapply nth_error_string_Some_lt_len in Hch.
      exact Hch.
    }
    specialize (Hall i Hi2).
    destruct Hall as [a [b [c [Hi0 [Hi1 [Hi2' D]]]]]].
    assert (E01:
      nth_error_string
        ("qwertyuiopasdfghjklzxcvbnmwaaaaabbbbccccdeeeddddccccbbbbaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddccccaabcabcabcabcabcabcabcabcadbcabcabcabcaaccccddddaaaabbbbccccddddaaaabbbbccccddddabbcabcabertlyuiopasdfghjkldzxcvb"%string)
        i =
      nth_error_string
        ("qwertyuiopasdfghjklzxcvbnmwaaaaabbbbccccdeeeddddccccbbbbaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddccccaabcabcabcabcabcabcabcabcadbcabcabcabcaaccccddddaaaabbbbccccddddaaaabbbbccccddddabbcabcabertlyuiopasdfghjkldzxcvb"%string)
        (i + 1)).
    { reflexivity. }
    rewrite Hi0 in E01.
    rewrite Hi1 in E01.
    inversion E01; subst.
    destruct D as [Hab _].
    contradiction.
Qed.