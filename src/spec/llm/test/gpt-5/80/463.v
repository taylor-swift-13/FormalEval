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

Lemma nth_error_string_some_length : forall s n a, nth_error_string s n = Some a -> n < String.length s.
Proof.
  induction s as [| ch s' IH]; intros n a Hnth; simpl in Hnth.
  - discriminate.
  - destruct n as [| n'].
    + simpl. lia.
    + apply IH in Hnth. simpl. lia.
Qed.

Example test_is_happy_long: is_happy_spec ("3112233aaccckgeaaaaabbbbccccdeeeddddccccbbbbaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddccccaabcabcabcabcabcabcabcabcadbcabcabcabcaaccccddddaaaabbbbccccddddaaaabbbbccccddddaabbcabcaboNtlLNRbcabcabcabcabcabcabcabbcabcabcababcabbbaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddccccaaaabbbbccccddddaaaabbbbccaccdddd44551122334455667755656778899006abcabb65677889900"%string) false.
Proof.
  right.
  split.
  - reflexivity.
  - unfold not; intros H.
    unfold happy_prop in H.
    destruct H as [Hlen Hall].
    specialize (Hall 1).
    simpl in Hall.
    assert (nth_error_string ("3112233aaccckgeaaaaabbbbccccdeeeddddccccbbbbaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddccccaabcabcabcabcabcabcabcabcadbcabcabcabcaaccccddddaaaabbbbccccddddaaaabbbbccccddddaabbcabcaboNtlLNRbcabcabcabcabcabcabcabbcabcabcababcabbbaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddccccaaaabbbbccccddddaaaabbbbccaccdddd44551122334455667755656778899006abcabb65677889900"%string) 3 = Some ("2"%char)) as Hn3.
    { simpl. reflexivity. }
    pose proof (nth_error_string_some_length ("3112233aaccckgeaaaaabbbbccccdeeeddddccccbbbbaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddccccaabcabcabcabcabcabcabcabcadbcabcabcabcaaccccddddaaaabbbbccccddddaaaabbbbccccddddaabbcabcaboNtlLNRbcabcabcabcabcabcabcabbcabcabcababcabbbaaaaaaaabbbbccccdeeeddddccccbbbbaaaaeeeedddccccaaeeeedddccccaaaabbbbccccddddaaaabbbbccaccdddd44551122334455667755656778899006abcabb65677889900"%string) 3 ("2"%char) Hn3) as Hlt.
    apply Hall in Hlt.
    destruct Hlt as [a [b [c [H1 [H2 [H3 Hd]]]]]].
    simpl in H1. inversion H1; subst a.
    simpl in H2. inversion H2; subst b.
    simpl in H3. inversion H3; subst c.
    destruct Hd as [Hab [Hac Hbc]].
    apply Hab. reflexivity.
Qed.