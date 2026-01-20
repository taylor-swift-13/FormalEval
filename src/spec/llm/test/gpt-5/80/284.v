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

Lemma nth_error_string_Some_lt: forall s n ch, nth_error_string s n = Some ch -> n < String.length s.
Proof.
  induction s as [|a0 s' IH]; simpl; intros n ch H.
  - inversion H.
  - destruct n.
    + inversion H. lia.
    + apply IH in H. simpl. lia.
Qed.

Definition s_test :=
  "abcbcabcabcabcabcabcabcabcabcabcabcaabcabcabcabcabcabcabcabcabcabcabcabcabcabcabcabcabcbbbbaaaaeeeedddccccaaeeeedddccccabcabcabbcabcabcababcab"%string.

Example test_is_happy_long: is_happy_spec s_test false.
Proof.
  right.
  split.
  - reflexivity.
  - unfold not; intros H.
    unfold happy_prop in H.
    destruct H as [Hlen Hall].
    assert (E3: exists ch3, nth_error_string s_test 3 = Some ch3).
    { unfold s_test. simpl. eexists. reflexivity. }
    destruct E3 as [ch3 He3].
    pose proof (nth_error_string_Some_lt s_test 3 ch3 He3) as Hlt3.
    pose proof (Hall 1) as Hall1.
    assert (Hexists: exists a b c,
              nth_error_string s_test 1 = Some a /\
              nth_error_string s_test 2 = Some b /\
              nth_error_string s_test 3 = Some c /\
              distinct3 a b c).
    { apply Hall1. replace (1 + 2) with 3 by lia. exact Hlt3. }
    destruct Hexists as [a [b [c [H1 [H2 [H3 Hd]]]]]].
    assert (Heq13: nth_error_string s_test 1 = nth_error_string s_test 3).
    { unfold s_test. simpl. reflexivity. }
    assert (HeqSome: Some a = Some c).
    { rewrite <- H1. rewrite <- H3. exact Heq13. }
    injection HeqSome as Hac.
    destruct Hd as [_ [Hneq_ac _]].
    rewrite Hac in Hneq_ac.
    apply Hneq_ac. reflexivity.
Qed.