Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
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

Lemma nth_error_string_append_left :
  forall s1 s2 n,
    n < String.length s1 ->
    nth_error_string (String.append s1 s2) n = nth_error_string s1 n.
Proof.
  induction s1; intros s2 n Hlt; simpl in Hlt.
  - lia.
  - destruct n as [|n']; simpl.
    + reflexivity.
    + specialize (IHs1 s2 n').
      apply IHs1.
      lia.
Qed.

Lemma nth_error_string_append_right :
  forall s1 s2 n,
    String.length s1 <= n ->
    nth_error_string (String.append s1 s2) n = nth_error_string s2 (n - String.length s1).
Proof.
  induction s1; intros s2 n Hle; simpl in *.
  - simpl. now rewrite Nat.sub_0_r.
  - destruct n as [|n']; [lia|].
    simpl.
    apply IHs1.
    lia.
Qed.

Lemma length_append :
  forall s1 s2,
    String.length (String.append s1 s2) = String.length s1 + String.length s2.
Proof.
  induction s1; intros s2; simpl.
  - reflexivity.
  - rewrite IHs1. reflexivity.
Qed.

Example test_is_happy_single_a: is_happy_spec ("qwertyuiopasdfghjklzxcvbnmqwertlyuiopasdfghjklzqwertyuiopasdfghjklzxcvbnmqwertlyuiopasdfghjklzxcvbqwertyuiopasdfghjklzxcvbnmqwertyabcabuiopasdfghjkaaaaabbbdddccccaaeeeedddccccaabcabcabcabcabcabbcabcabcabcabcaaaaabbbbccccdeeeddddccccbbbbaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddccccaabcabcabcabcabcabcabcabcabcabcabcabcaabcabbcabcabcababcabbacabcabcababcabbbaaaaaaaabbbbccccdeeeddddccabcabcaabcccaaabbddeefffbcabcaabcabcabcabcabcabcabcabcabcabcabcabcabccbbbbaaaaeeeedddccccaaeeeedddccccqwe11223344556abcabcabcabcabcabcabcabcabcabaaaaabbbbccccdeeeddddccccbbbbaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddccccaceabcabcabcabbcabcabcab65677889900aad4dbbccddeeaabbccddeertyuiopasdfghjklzxcvbnmqwertyuiopasdfghjklzxcvblzxcvbdddccccalzxcvb"%string) false.
Proof.
  right.
  split.
  - reflexivity.
  - unfold not; intros H.
    unfold happy_prop in H.
    destruct H as [Hlen Hall].
    set (p := "qwertyuiopasdfghjklzxcvbnmqwertlyuiopasdfghjklzqwertyuiopasdfghjklzxcvbnmqwertlyuiopasdfghjklzxcvbqwertyuiopasdfghjklzxcvbnmqwertyabcabuiopasdfghjk"%string).
    set (t := "aaaaabbbdddccccaaeeeedddccccaabcabcabcabcabcabbcabcabcabcabcaaaaabbbbccccdeeeddddccccbbbbaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddccccaabcabcabcabcabcabcabcabcabcabcabcabcaabcabbcabcabcababcabbacabcabcababcabbbaaaaaaaabbbbccccdeeeddddccabcabcaabcccaaabbddeefffbcabcaabcabcabcabcabcabcabcabcabcabcabcabcabccbbbbaaaaeeeedddccccaaeeeedddccccqwe11223344556abcabcabcabcabcabcabcabcabcabaaaaabbbbccccdeeeddddccccbbbbaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddccccaceabcabcabcabbcabcabcab65677889900aad4dbbccddeeaabbccddeertyuiopasdfghjklzxcvbnmqwertyuiopasdfghjklzxcvblzxcvbdddccccalzxcvb"%string).
    assert (Hconcat: ("qwertyuiopasdfghjklzxcvbnmqwertlyuiopasdfghjklzqwertyuiopasdfghjklzxcvbnmqwertlyuiopasdfghjklzxcvbqwertyuiopasdfghjklzxcvbnmqwertyabcabuiopasdfghjkaaaaabbbdddccccaaeeeedddccccaabcabcabcabcabcabbcabcabcabcabcaaaaabbbbccccdeeeddddccccbbbbaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddccccaabcabcabcabcabcabcabcabcabcabcabcabcaabcabbcabcabcababcabbacabcabcababcabbbaaaaaaaabbbbccccdeeeddddccabcabcaabcccaaabbddeefffbcabcaabcabcabcabcabcabcabcabcabcabcabcabcabccbbbbaaaaeeeedddccccaaeeeedddccccqwe11223344556abcabcabcabcabcabcabcabcabcabaaaaabbbbccccdeeeddddccccbbbbaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddccccaceabcabcabcabbcabcabcab65677889900aad4dbbccddeeaabbccddeertyuiopasdfghjklzxcvbnmqwertyuiopasdfghjklzxcvblzxcvbdddccccalzxcvb"%string) = String.append p t) by reflexivity.
    set (i := String.length p).
    assert (Htlen3: 3 <= String.length t) by (simpl; lia).
    assert (Hi: i + 2 < String.length (String.append p t)).
    { unfold i. rewrite length_append. lia. }
    rewrite Hconcat in Hall.
    specialize (Hall i).
    specialize (Hall Hi).
    destruct Hall as [a [b [c [Ha [Hb [Hc Hd]]]]]].
    assert (Hle0: String.length p <= i) by (unfold i; lia).
    assert (Hle1: String.length p <= i + 1) by (unfold i; lia).
    assert (Hle2: String.length p <= i + 2) by (unfold i; lia).
    rewrite (nth_error_string_append_right p t i Hle0) in Ha.
    rewrite (nth_error_string_append_right p t (i + 1) Hle1) in Hb.
    rewrite (nth_error_string_append_right p t (i + 2) Hle2) in Hc.
    unfold i in Ha, Hb, Hc.
    rewrite Nat.sub_diag in Ha.
    rewrite Nat.add_comm in Hb.
    rewrite Nat.add_comm in Hc.
    rewrite Nat.add_sub in Hb.
    rewrite Nat.add_sub in Hc.
    simpl in Ha.
    simpl in Hb.
    simpl in Hc.
    inversion Ha; subst a.
    inversion Hb; subst b.
    inversion Hc; subst c.
    destruct Hd as [Hab [Hac Hbc]].
    apply Hab. reflexivity.
Qed.