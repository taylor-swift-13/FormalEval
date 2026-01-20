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
  induction s as [| ch s' IH]; intros n a H.
  - simpl in H. discriminate.
  - simpl in H.
    destruct n as [| n'].
    + inversion H; simpl; lia.
    + apply IH in H. simpl. lia.
Qed.

Example test_is_happy_long: is_happy_spec ("abcbcabcabcabcabcabcabcabcabcabcabcabcaaaabcabcabcaaaaaabbbbccccdaeeeddddccccbbbbaaaaeeabcabcabaaccccddddaaaabbbbccccddddaaaabbbbccccddddcabcabcabcabcabcabcabcabcaaaaabbbbccccdeeeddddccccbbbbaaaaaeeabcabcabcabcabcabcabcabcaaabcabcabcabcabcabcabcabcabcabcabcabcabcabcabcabcabbcabcabcabcabcabcabcabcabeedddcaabcabcabcabcabcabeedddcbcabcabcabcabcabcabcabcabcabcabcabcabcabaabbbbccaccdeeeddddccccbbbbaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddccccaabcabcacbcabcabcabcabcabcabcabcabcabcabcabbcabcabcababcab"%string) false.
Proof.
  right.
  split.
  - reflexivity.
  - unfold not; intros H.
    unfold happy_prop in H.
    destruct H as [_ Hall].
    assert (H1: nth_error_string ("abcbcabcabcabcabcabcabcabcabcabcabcabcaaaabcabcabcaaaaaabbbbccccdaeeeddddccccbbbbaaaaeeabcabcabaaccccddddaaaabbbbccccddddaaaabbbbccccddddcabcabcabcabcabcabcabcabcaaaaabbbbccccdeeeddddccccbbbbaaaaaeeabcabcabcabcabcabcabcabcaaabcabcabcabcabcabcabcabcabcabcabcabcabcabcabcabcabbcabcabcabcabcabcabcabcabeedddcaabcabcabcabcabcabeedddcbcabcabcabcabcabcabcabcabcabcabcabcabcabaabbbbccaccdeeeddddccccbbbbaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddccccaabcabcacbcabcabcabcabcabcabcabcabcabcabcabbcabcabcababcab"%string) 1 = Some ("b"%char)).
    { simpl. reflexivity. }
    assert (H3: nth_error_string ("abcbcabcabcabcabcabcabcabcabcabcabcabcaaaabcabcabcaaaaaabbbbccccdaeeeddddccccbbbbaaaaeeabcabcabaaccccddddaaaabbbbccccddddaaaabbbbccccddddcabcabcabcabcabcabcabcabcaaaaabbbbccccdeeeddddccccbbbbaaaaaeeabcabcabcabcabcabcabcabcaaabcabcabcabcabcabcabcabcabcabcabcabcabcabcabcabcabbcabcabcabcabcabcabcabcabeedddcaabcabcabcabcabcabeedddcbcabcabcabcabcabcabcabcabcabcabcabcabcabaabbbbccaccdeeeddddccccbbbbaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddccccaabcabcacbcabcabcabcabcabcabcabcabcabcabcabbcabcabcababcab"%string) 3 = Some ("b"%char)).
    { simpl. reflexivity. }
    assert (Hlt: 3 < String.length ("abcbcabcabcabcabcabcabcabcabcabcabcabcaaaabcabcabcaaaaaabbbbccccdaeeeddddccccbbbbaaaaeeabcabcabaaccccddddaaaabbbbccccddddaaaabbbbccccddddcabcabcabcabcabcabcabcabcaaaaabbbbccccdeeeddddccccbbbbaaaaaeeabcabcabcabcabcabcabcabcaaabcabcabcabcabcabcabcabcabcabcabcabcabcabcabcabcabbcabcabcabcabcabcabcabcabeedddcaabcabcabcabcabcabeedddcbcabcabcabcabcabcabcabcabcabcabcabcabcabaabbbbccaccdeeeddddccccbbbbaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddccccaabcabcacbcabcabcabcabcabcabcabcabcabcabcabbcabcabcababcab"%string)).
    { apply nth_error_string_Some_lt_len with (a := "b"%char) in H3. exact H3. }
    specialize (Hall 1).
    assert (Hex: exists a b c,
              nth_error_string ("abcbcabcabcabcabcabcabcabcabcabcabcabcaaaabcabcabcaaaaaabbbbccccdaeeeddddccccbbbbaaaaeeabcabcabaaccccddddaaaabbbbccccddddaaaabbbbccccddddcabcabcabcabcabcabcabcabcaaaaabbbbccccdeeeddddccccbbbbaaaaaeeabcabcabcabcabcabcabcabcaaabcabcabcabcabcabcabcabcabcabcabcabcabcabcabcabcabbcabcabcabcabcabcabcabcabeedddcaabcabcabcabcabcabeedddcbcabcabcabcabcabcabcabcabcabcabcabcabcabaabbbbccaccdeeeddddccccbbbbaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddccccaabcabcacbcabcabcabcabcabcabcabcabcabcabcabbcabcabcababcab"%string) 1 = Some a /\
              nth_error_string ("abcbcabcabcabcabcabcabcabcabcabcabcabcaaaabcabcabcaaaaaabbbbccccdaeeeddddccccbbbbaaaaeeabcabcabaaccccddddaaaabbbbccccddddaaaabbbbccccddddcabcabcabcabcabcabcabcabcaaaaabbbbccccdeeeddddccccbbbbaaaaaeeabcabcabcabcabcabcabcabcaaabcabcabcabcabcabcabcabcabcabcabcabcabcabcabcabcabbcabcabcabcabcabcabcabcabeedddcaabcabcabcabcabcabeedddcbcabcabcabcabcabcabcabcabcabcabcabcabcabaabbbbccaccdeeeddddccccbbbbaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddccccaabcabcacbcabcabcabcabcabcabcabcabcabcabcabbcabcabcababcab"%string) 2 = Some b /\
              nth_error_string ("abcbcabcabcabcabcabcabcabcabcabcabcabcaaaabcabcabcaaaaaabbbbccccdaeeeddddccccbbbbaaaaeeabcabcabaaccccddddaaaabbbbccccddddaaaabbbbccccddddcabcabcabcabcabcabcabcabcaaaaabbbbccccdeeeddddccccbbbbaaaaaeeabcabcabcabcabcabcabcabcaaabcabcabcabcabcabcabcabcabcabcabcabcabcabcabcabcabbcabcabcabcabcabcabcabcabeedddcaabcabcabcabcabcabeedddcbcabcabcabcabcabcabcabcabcabcabcabcabcabaabbbbccaccdeeeddddccccbbbbaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddccccaabcabcacbcabcabcabcabcabcabcabcabcabcabcabbcabcabcababcab"%string) 3 = Some c /\
              distinct3 a b c).
    { apply Hall. simpl. exact Hlt. }
    destruct Hex as [a [b [c [E1 [E2 [E3 Hd]]]]]].
    rewrite E1 in H1. inversion H1. subst a.
    rewrite E3 in H3. inversion H3. subst c.
    destruct Hd as [_ [Hac _]].
    apply Hac. reflexivity.
Qed.