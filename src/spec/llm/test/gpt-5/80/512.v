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

Lemma nth_error_string_notNone_lt_len :
  forall s n, nth_error_string s n <> None -> n < String.length s.
Proof.
  intros s.
  induction s as [|a s' IH]; intros n H.
  - simpl in H. contradiction.
  - destruct n as [|n'].
    + simpl. lia.
    + simpl in H. specialize (IH n' H). simpl. lia.
Qed.

Example test_is_happy_long: is_happy_spec ("FeQYRFWWaaaaabbbbccccdeeeddddccabcccaaabbddeefffccbbbbaaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeeddqwertyuiopasdfghjklzxcvbnmqwertlyuiopasdfghjklzxcvbqwertyuiopasdfghjklzxcvbnmqwertyabcabuiopasdfghjkaaaaabbbdddcqwertyuiopasdfghjklzxcvbnmqwertlyuiopasdfghjklzxcvbqwertyuiopasdfghjklzxcvbnmqwertyabcabuiopasdfghjkaaaaabbbdddccccaaeeeedddccccaabcabcabcabcabcabbcabcabcabcacbcaaaaabbbbccccdeeeddddccccbbbbaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddccccaabcabcabcabcabcabcabcabcabcabcabcabcaabcabbcabcabcababcabbcabcabcababcabbbaaaaaaaabbbbccccdeeeddddccabcabcaabcccaaabbddeefffbcabcaabcabcabcabcabcabcabcabcabcabcabcabcabccb11223344556abcabcabcabcabcabcabcabcabcaabcabcabcabbcabcabcabU"%string) false.
Proof.
  right.
  split.
  - reflexivity.
  - unfold not; intros H.
    unfold happy_prop in H.
    destruct H as [Hlen Hall].
    assert (Hlt: 8 < String.length ("FeQYRFWWaaaaabbbbccccdeeeddddccabcccaaabbddeefffccbbbbaaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeeddqwertyuiopasdfghjklzxcvbnmqwertlyuiopasdfghjklzxcvbqwertyuiopasdfghjklzxcvbnmqwertyabcabuiopasdfghjkaaaaabbbdddcqwertyuiopasdfghjklzxcvbnmqwertlyuiopasdfghjklzxcvbqwertyuiopasdfghjklzxcvbnmqwertyabcabuiopasdfghjkaaaaabbbdddccccaaeeeedddccccaabcabcabcabcabcabbcabcabcabcacbcaaaaabbbbccccdeeeddddccccbbbbaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddccccaabcabcabcabcabcabcabcabcabcabcabcabcaabcabbcabcabcababcabbcabcabcababcabbbaaaaaaaabbbbccccdeeeddddccabcabcaabcccaaabbddeefffbcabcaabcabcabcabcabcabcabcabcabcabcabcabcabccb11223344556abcabcabcabcabcabcabcabcabcaabcabcabcabbcabcabcabU"%string)).
    { apply nth_error_string_notNone_lt_len. simpl. discriminate. }
    specialize (Hall 6).
    specialize (Hall Hlt).
    destruct Hall as [a [b [c [H6 [H7 [H8 Hdist]]]]]].
    simpl in H6.
    simpl in H7.
    inversion H6; subst a.
    inversion H7; subst b.
    destruct Hdist as [Hab [Hac Hbc]].
    apply Hab.
    reflexivity.
Qed.