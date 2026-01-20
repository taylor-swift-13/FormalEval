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
  forall s n x, nth_error_string s n = Some x -> n < String.length s.
Proof.
  induction s as [| a s' IH]; intros n x H.
  - simpl in H. discriminate.
  - destruct n.
    + simpl in H. inversion H. simpl. lia.
    + simpl in H. specialize (IH n x H). simpl. lia.
Qed.

Example test_is_happy_large: is_happy_spec ("qwerty1121122334455667755656778abcabcaabccabcdefgabcdefgcdefgabcdefgabcdeaaccccddddadaaabbbbccccddddaaaabbbbccccddddfgcdefgabcdefgaaabbddeefffbcabcaabcabcabcabcabcabcabcabcabcabcabcabcabaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddcaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddcccca89900233445566775565677889900uiopasdfghjklzxcvbnmqwertyuiopasvdfghjklzxcvb"%string) false.
Proof.
  right.
  split.
  - reflexivity.
  - unfold not; intros H.
    unfold happy_prop in H.
    destruct H as [Hlen Hall].
    set (s := "qwerty1121122334455667755656778abcabcaabccabcdefgabcdefgcdefgabcdefgabcdeaaccccddddadaaabbbbccccddddaaaabbbbccccddddfgcdefgabcdefgaaabbddeefffbcabcaabcabcabcabcabcabcabcabcabcabcabcabcabaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddcaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddcccca89900233445566775565677889900uiopasdfghjklzxcvbnmqwertyuiopasvdfghjklzxcvb"%string).
    assert (Hn8: nth_error_string s 8 = Some ("2"%char)).
    { subst s. simpl. reflexivity. }
    assert (Hpre: 6 + 2 < String.length s).
    { eapply nth_error_string_Some_lt_length; eauto. }
    specialize (Hall 6 Hpre).
    destruct Hall as [a [b [c [Ha [Hb [Hc Hdistinct]]]]]].
    subst s.
    simpl in Ha, Hb, Hc.
    inversion Ha; subst a.
    inversion Hb; subst b.
    destruct Hdistinct as [Hab [Hac Hbc]].
    apply Hab. reflexivity.
Qed.