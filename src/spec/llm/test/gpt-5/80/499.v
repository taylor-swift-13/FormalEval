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

Lemma nth_error_string_some_implies_lt_length :
  forall s n a, nth_error_string s n = Some a -> n < String.length s.
Proof.
  intros s.
  induction s as [| ch s' IH].
  - intros n a H. simpl in H. discriminate.
  - intros [|n'] a H.
    + simpl in H. inversion H; subst. simpl. lia.
    + simpl in H. specialize (IH n' a H). simpl. lia.
Qed.

Example test_is_happy_single_a: is_happy_spec ("ab112233445qwe11223344556abcabcabcabcabcabcabcabcabcabaaaaabbbbccccdeeeddddccccbbbbaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddccccaceabcabcabcabbcabcabcab65677889900aad4dbbccddeeaabbccddeertyuiopasdfghjklzxcvbnmqwertyuiopasdfghjklzxcvb56677556677889900ccccddddaaaabbbbccccddddaaaabbbbccccddddcabcabcabcabcabcabcabcabcaaaaabbbbccccdeeeddddccccbbbbaaaaeeabcabcabcabcabcabcabcabcaaabcabcabcabcabcabcabcabcabcabcabcabcabcabcabcabcabbcabcabcabcabcabcabcabcabeedddcabcabcabcabcabcabeedddcbcabcabcabcabcabcabcabcabcabcabcabcabcabaabbbbccaccdeeeddddccccbbbbaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddccccaabcabcabcabcabcabcabcabcabcabcabcabcabcabbcabcabcababcab"%string) false.
Proof.
  right.
  split.
  - reflexivity.
  - unfold not; intros H.
    unfold happy_prop in H.
    destruct H as [Hlen Hall].
    specialize (Hall 2%nat).
    assert (Hn4: nth_error_string ("ab112233445qwe11223344556abcabcabcabcabcabcabcabcabcabaaaaabbbbccccdeeeddddccccbbbbaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddccccaceabcabcabcabbcabcabcab65677889900aad4dbbccddeeaabbccddeertyuiopasdfghjklzxcvbnmqwertyuiopasdfghjklzxcvb56677556677889900ccccddddaaaabbbbccccddddaaaabbbbccccddddcabcabcabcabcabcabcabcabcaaaaabbbbccccdeeeddddccccbbbbaaaaeeabcabcabcabcabcabcabcabcaaabcabcabcabcabcabcabcabcabcabcabcabcabcabcabcabcabbcabcabcabcabcabcabcabcabeedddcabcabcabcabcabcabeedddcbcabcabcabcabcabcabcabcabcabcabcabcabcabaabbbbccaccdeeeddddccccbbbbaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddccccaabcabcabcabcabcabcabcabcabcabcabcabcabcabbcabcabcababcab"%string) 4 = Some ("2"%char)).
    { simpl. reflexivity. }
    assert (Hlt : 2 + 2 < String.length ("ab112233445qwe11223344556abcabcabcabcabcabcabcabcabcabaaaaabbbbccccdeeeddddccccbbbbaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddccccaceabcabcabcabbcabcabcab65677889900aad4dbbccddeeaabbccddeertyuiopasdfghjklzxcvbnmqwertyuiopasdfghjklzxcvb56677556677889900ccccddddaaaabbbbccccddddaaaabbbbccccddddcabcabcabcabcabcabcabcabcaaaaabbbbccccdeeeddddccccbbbbaaaaeeabcabcabcabcabcabcabcabcaaabcabcabcabcabcabcabcabcabcabcabcabcabcabcabcabcabbcabcabcabcabcabcabcabcabeedddcabcabcabcabcabcabeedddcbcabcabcabcabcabcabcabcabcabcabcabcabcabaabbbbccaccdeeeddddccccbbbbaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddccccaabcabcabcabcabcabcabcabcabcabcabcabcabcabbcabcabcababcab"%string)).
    { replace (2 + 2) with 4 by lia.
      eapply nth_error_string_some_implies_lt_length; exact Hn4. }
    specialize (Hall Hlt).
    destruct Hall as [a [b [c [Ha [Hb [Hc Hd]]]]]].
    simpl in Ha. inversion Ha. subst.
    simpl in Hb. inversion Hb. subst.
    destruct Hd as [Hab [Hac Hbc]].
    apply Hab. reflexivity.
Qed.