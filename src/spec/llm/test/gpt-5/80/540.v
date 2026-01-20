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

Lemma nth_error_string_some_length :
  forall s n a, nth_error_string s n = Some a -> n < String.length s.
Proof.
  induction s as [|ch s' IH]; intros n a H; simpl in H.
  - discriminate H.
  - destruct n as [|n']; simpl in H.
    + inversion H; simpl; lia.
    + apply IH in H. simpl. lia.
Qed.

Example test_is_happy_long: is_happy_spec ("1abababababababababababababababababababababababaaaaabbbbccccdeeeddddccccbbbbaaaaeeabcabcabaaccccddddaaaabbbbccccddddaaaabbbbccccddddcababcabcabcabcabcabcabcabcabcaaaaabbbbccccdeeedddddccccbbbbaaaaeeabcabcabcabcabcabcabcabcabcabcabcabcabcabcabcabcabeedddcabcabcaaccccddddaaaaaabbbabccccdeeeddddccccbbabcbcabcabcabcabcabcabcabcabcabcabcabcaaaaabbbbccccdeeeddddccccbbbbaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddccccaabcabcabcabcabcabcabcabcabcabcabcabcabcabbcabcabcababcabbbabaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddccccaaaabbbbccccddddaaaabbbbccaccddddabcabcabcabeedddcab12237344557667755656777889900"%string) false.
Proof.
  right.
  split.
  - reflexivity.
  - unfold not; intros H.
    unfold happy_prop in H.
    destruct H as [Hlen Hforall].
    assert (Hlt: 1 + 2 < String.length ("1abababababababababababababababababababababababaaaaabbbbccccdeeeddddccccbbbbaaaaeeabcabcabaaccccddddaaaabbbbccccddddaaaabbbbccccddddcababcabcabcabcabcabcabcabcabcaaaaabbbbccccdeeedddddccccbbbbaaaaeeabcabcabcabcabcabcabcabcabcabcabcabcabcabcabcabcabeedddcabcabcaaccccddddaaaaaabbbabccccdeeeddddccccbbabcbcabcabcabcabcabcabcabcabcabcabcabcaaaaabbbbccccdeeeddddccccbbbbaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddccccaabcabcabcabcabcabcabcabcabcabcabcabcabcabbcabcabcababcabbbabaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddccccaaaabbbbccccddddaaaabbbbccaccddddabcabcabcabeedddcab12237344557667755656777889900"%string)).
    {
      assert (Heq3: nth_error_string ("1abababababababababababababababababababababababaaaaabbbbccccdeeeddddccccbbbbaaaaeeabcabcabaaccccddddaaaabbbbccccddddaaaabbbbccccddddcababcabcabcabcabcabcabcabcabcaaaaabbbbccccdeeedddddccccbbbbaaaaeeabcabcabcabcabcabcabcabcabcabcabcabcabcabcabcabcabeedddcabcabcaaccccddddaaaaaabbbabccccdeeeddddccccbbabcbcabcabcabcabcabcabcabcabcabcabcabcaaaaabbbbccccdeeeddddccccbbbbaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddccccaabcabcabcabcabcabcabcabcabcabcabcabcabcabbcabcabcababcabbbabaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddccccaaaabbbbccccddddaaaabbbbccaccddddabcabcabcabeedddcab12237344557667755656777889900"%string) 3 = Some ("a"%char)).
      { simpl. reflexivity. }
      pose proof (nth_error_string_some_length _ _ _ Heq3) as Hlt3.
      lia.
    }
    specialize (Hforall 1 Hlt).
    destruct Hforall as [a [b [c [Ha [Hb [Hc Hdistinct]]]]]].
    simpl in Ha. inversion Ha; subst.
    simpl in Hb. inversion Hb; subst.
    simpl in Hc. inversion Hc; subst.
    destruct Hdistinct as [Hab [Hac Hbc]].
    apply Hac.
    reflexivity.
Qed.