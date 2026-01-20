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

Lemma length_append: forall s1 s2, String.length (String.append s1 s2) = String.length s1 + String.length s2.
Proof.
  induction s1; intros s2; simpl.
  - reflexivity.
  - rewrite IHs1. reflexivity.
Qed.

Lemma nth_error_string_append_left:
  forall s1 s2 n,
    n < String.length s1 ->
    nth_error_string (String.append s1 s2) n = nth_error_string s1 n.
Proof.
  induction s1; intros s2 n H.
  - simpl in H. lia.
  - simpl. destruct n.
    + reflexivity.
    + simpl in H. apply IHs1. lia.
Qed.

Lemma nth_error_string_append_right:
  forall s1 s2 n,
    String.length s1 <= n ->
    nth_error_string (String.append s1 s2) n = nth_error_string s2 (n - String.length s1).
Proof.
  induction s1; intros s2 n H.
  - simpl. rewrite Nat.sub_0_r. reflexivity.
  - simpl in *. destruct n.
    + lia.
    + apply IHs1. lia.
Qed.

Definition s_prefix : string :=
  "abcbcabcabcabcabcabcabcabcabcabcabcabcaaaaabbbbccccdeeeddddccccbbbbaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddccccaabcabcabcabcabcabcabcab11223344556abcabcabcabcabcabcabcabcabcabaaaaabbbbccccdeeebddddccccbbbbaaaaaaaabbbbeccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddccccaceabcabcabcabbcabcabcab656778899"%string.

Definition s_suffix_tail : string :=
  "aad4dbbccddeeaabbccddeecabcabcabcabcabcabbcabcabcababcabNuqZCZBVKR"%string.

Definition s_suffix : string :=
  String "0"%char (String "0"%char (String "a"%char s_suffix_tail)).

Definition s_long : string := String.append s_prefix s_suffix.

Example test_is_happy_long: is_happy_spec s_long false.
Proof.
  right.
  split.
  - reflexivity.
  - unfold not; intros H.
    unfold happy_prop in H.
    destruct H as [Hlen Hall].
    set (i := String.length s_prefix).
    assert (Hi: i + 2 < String.length s_long).
    { unfold i, s_long.
      rewrite length_append.
      simpl.
      lia.
    }
    specialize (Hall i Hi).
    destruct Hall as [a [b [c [Ha [Hb [Hc Hd]]]]]].
    assert (Ha0: nth_error_string s_long i = Some ("0"%char)).
    { unfold s_long, i.
      assert (Hle: String.length s_prefix <= String.length s_prefix) by lia.
      rewrite (nth_error_string_append_right s_prefix s_suffix (String.length s_prefix) Hle).
      simpl. reflexivity.
    }
    assert (Hb0: nth_error_string s_long (i + 1) = Some ("0"%char)).
    { unfold s_long, i.
      assert (Hle: String.length s_prefix <= String.length s_prefix + 1) by lia.
      rewrite (nth_error_string_append_right s_prefix s_suffix (String.length s_prefix + 1) Hle).
      simpl. reflexivity.
    }
    rewrite Ha0 in Ha.
    rewrite Hb0 in Hb.
    inversion Ha; subst a.
    inversion Hb; subst b.
    destruct Hd as [Hab _].
    apply Hab. reflexivity.
Qed.