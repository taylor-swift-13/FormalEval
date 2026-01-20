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
  forall s n ch, nth_error_string s n = Some ch -> n < String.length s.
Proof.
  induction s as [| a s' IH]; intros [| n'] ch H; simpl in H; try discriminate.
  - simpl. lia.
  - apply IH in H. simpl. lia.
Qed.

Example test_is_happy_large_false: is_happy_spec ("aaaaabbbbccccdeee112233445356abcabcabcaaaaabbbbccccdeeeddddccaaadadbbccddeeaabbccddeebcccaaabbddeefffccbbbbaaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeecedddccccaabcabcabcabcabcabbabcabcabcabcabcabcabcabcabcabcabbcabcabcab6567788aaaaabbbbccccddddaaaabbbbccdccddddaaaabbbbccccdddd900ddddccccbbbbaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddccccaabcabcabcabcabcabcabcabcadbcabcabcabcaaccccddddaaaabbbbccccddddaaaabbbbccccddddaabbcabcab"%string) false.
Proof.
  right.
  split.
  - reflexivity.
  - unfold not; intros H.
    set (s := "aaaaabbbbccccdeee112233445356abcabcabcaaaaabbbbccccdeeeddddccaaadadbbccddeeaabbccddeebcccaaabbddeefffccbbbbaaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeecedddccccaabcabcabcabcabcabbabcabcabcabcabcabcabcabcabcabcabbcabcabcab6567788aaaaabbbbccccddddaaaabbbbccdccddddaaaabbbbccccdddd900ddddccccbbbbaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddccccaabcabcabcabcabcabcabcabcadbcabcabcabcaaccccddddaaaabbbbccccddddaaaabbbbccccddddaabbcabcab"%string) in H |- *.
    unfold happy_prop in H.
    destruct H as [Hlen Hforall].
    assert (Hlt: 2 < String.length s).
    { assert (nth_error_string s 2 = Some "a"%char) by (unfold s; simpl; reflexivity).
      eapply nth_error_string_Some_lt; eauto.
    }
    specialize (Hforall 0).
    assert (0 + 2 < String.length s) by lia.
    specialize (Hforall H).
    destruct Hforall as [a [b [c [E0 [E1 [E2 Hdist]]]]]].
    unfold s in E0, E1, E2.
    simpl in E0, E1, E2.
    inversion E0; subst.
    inversion E1; subst.
    inversion E2; subst.
    destruct Hdist as [Hab [Hac Hbc]].
    apply Hab; reflexivity.
Qed.