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

Lemma nth_error_string_Some_lt_len :
  forall s n a, nth_error_string s n = Some a -> n < String.length s.
Proof.
  induction s as [|x s' IH]; intros n a H; simpl in *.
  - discriminate.
  - destruct n.
    + lia.
    + eapply lt_n_S. eapply IH. exact H.
Qed.

Definition long_str : string :=
"abcabcabcabcabbcabcabcabcadbcabcabcabcaaccccddddaaaabbbbccccddddabcbcabcabcabcabcabcabcabcabcabcabcabcaaaabcabcabcaaaaaabbbbccccdaeeeddddccccbbbbaaaaeeabcabcabaaccccddddaaaabbbbccccddddaaaabbbbccccddddcabcabcabcabcabcabcabcabcaaaaabbbbccccdeeeddddccccbbbbaaaaaeeabcabcabcabcabcabcabcabcaaabcabcabcabcabcabcabcabcabcabcabcabcabcabcabcabcabbcabcabcabcabcabcabcabcabeedddcabcabcabcabcabcabeedddcbcabcabcabcabcabcabcabcabcabcabcabcabcabaabbbbccaccdeeeddddccccbbbbaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddccccaabcabcabcabcabcabcabcabcabcabcabcabcabcabbqwertyuiopasdfghjklzxcvbnmqwertlyuiopasdfghjklzxcvbqwertyuiopasdfghjklzxcvbnmqwertyabcabuiopasdfghjkaaaaabbbdddccccaaeeeedddccccaabcabcabcabcabcabbcabcaabcdefgabcdefgcdefga7889900uiopasdfghjcklzxcvbnmqwertyuiopasdfghjklzxcvbfgabcdefgbcabcacbcaaaaabbbbccccdeeeddddccccbbbbaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddccccaabcabcabcabcabcabcabcabcabcabcabcabcaabcabbcabcabcababcabbcabcabcababcabbbaaaaaaaabbbbccccdeeeddddccabcabcaabcaccaaabbddeefffbcabcaabcabcabcabcabcabcabcabcabcabcabcabcabccb11223344556abcabcabcabcabcabcabcabcabcabaaaaabbbbccccdeeeddddccccbbbbaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddccccacabcabcabcabbcabcabcab65677889900aad4dbbccddeeaabbccddeebbbaaaaeeeedddccccaaeeeedddccccalzxcvbcabcacbcababcabaaabbbbccccddaaaaabbbbccccdeeeddddccccbbbbaaaaeeabcabcabcabcabcabcabcabcabcabcabcabcabcadcabcabcabeedddcddabbcabcab"%string.

Example test_is_happy_long: is_happy_spec long_str false.
Proof.
  right.
  split.
  - reflexivity.
  - unfold not; intros H.
    unfold happy_prop in H.
    destruct H as [_ Hall].
    assert (E14: nth_error_string long_str 14 = Some "b"%char) by (simpl; reflexivity).
    apply (nth_error_string_Some_lt_len long_str 14 ("b"%char)) in E14.
    specialize (Hall 12).
    specialize (Hall E14).
    destruct Hall as [a [b [c [Ha [Hb [Hc Hdistinct]]]]]].
    simpl in Ha, Hb, Hc.
    inversion Ha; subst.
    inversion Hb; subst.
    inversion Hc; subst.
    destruct Hdistinct as [_ [_ Hbc]].
    apply Hbc; reflexivity.
Qed.