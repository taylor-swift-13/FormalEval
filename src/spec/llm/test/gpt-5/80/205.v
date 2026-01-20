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

Lemma nth_error_string_Some_lt :
  forall s n a, nth_error_string s n = Some a -> n < String.length s.
Proof.
  induction s as [|a' s' IH]; intros n a H; simpl in H.
  - inversion H.
  - simpl.
    destruct n.
    + inversion H; lia.
    + eapply IH in H. lia.
Qed.

Example test_is_happy_long:
  is_happy_spec
    ("abcbcabcabcabcabcabcabcabcabcabcabcabcaaaaabbbbccaccdeeeddddccccbbbbaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddccccaabcabcabcabcabcabcabcabcabcabcabcabcabcabbcabcabcababcab"%string)
    false.
Proof.
  right.
  split.
  - reflexivity.
  - unfold not; intros H.
    unfold happy_prop in H.
    destruct H as [Hlen Hall].
    assert (nth_error_string
              ("abcbcabcabcabcabcabcabcabcabcabcabcabcaaaaabbbbccaccdeeeddddccccbbbbaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddccccaabcabcabcabcabcabcabcabcabcabcabcabcabcabbcabcabcababcab"%string)
              3
            = Some ("b"%char)) as H3val.
    { simpl. reflexivity. }
    assert (3 < String.length
                ("abcbcabcabcabcabcabcabcabcabcabcabcabcaaaaabbbbccaccdeeeddddccccbbbbaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddccccaabcabcabcabcabcabcabcabcabcabcabcabcabcabbcabcabcababcab"%string)) as H3lt.
    { eapply nth_error_string_Some_lt. exact H3val. }
    specialize (Hall 1).
    assert (1 + 2 < String.length
                ("abcbcabcabcabcabcabcabcabcabcabcabcabcaaaaabbbbccaccdeeeddddccccbbbbaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddccccaabcabcabcabcabcabcabcabcabcabcabcabcabcabbcabcabcababcab"%string)) as Hlt by lia.
    specialize (Hall Hlt).
    destruct Hall as (a & b & c & Ha & Hb & Hc & Hd).
    simpl in Ha. inversion Ha; subst a.
    simpl in Hb. inversion Hb; subst b.
    simpl in Hc. inversion Hc; subst c.
    destruct Hd as [_ [Hac _]].
    apply Hac. reflexivity.
Qed.