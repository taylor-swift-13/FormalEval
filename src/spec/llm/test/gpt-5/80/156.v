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

Lemma nth_error_string_Some_length:
  forall s n c, nth_error_string s n = Some c -> n < String.length s.
Proof.
  induction s; intros [|n] c H; simpl in H; try inversion H.
  - simpl. lia.
  - apply IHs in H. simpl. lia.
Qed.

Example test_is_happy_given: is_happy_spec ("abcabcabcabcabcabcabcabcabcabcabcabc11223344556abcabcabcabcabcabcabcabcabcabcabcabcabcabbcabcabcab65677889900abcabcabcabcab"%string) false.
Proof.
  right.
  split.
  - reflexivity.
  - unfold not; intros H.
    unfold happy_prop in H.
    destruct H as [_ Hall].
    set (i := 36).
    assert (H1: nth_error_string ("abcabcabcabcabcabcabcabcabcabcabcabc11223344556abcabcabcabcabcabcabcabcabcabcabcabcabcabbcabcabcab65677889900abcabcabcabcab"%string) i = Some "1"%char) by (subst i; reflexivity).
    assert (H2: nth_error_string ("abcabcabcabcabcabcabcabcabcabcabcabc11223344556abcabcabcabcabcabcabcabcabcabcabcabcabcabbcabcabcab65677889900abcabcabcabcab"%string) (i + 1) = Some "1"%char) by (subst i; reflexivity).
    assert (H3: nth_error_string ("abcabcabcabcabcabcabcabcabcabcabcabc11223344556abcabcabcabcabcabcabcabcabcabcabcabcabcabbcabcabcab65677889900abcabcabcabcab"%string) (i + 2) = Some "2"%char) by (subst i; reflexivity).
    pose proof (nth_error_string_Some_length _ _ _ H3) as Hlt.
    specialize (Hall i).
    specialize (Hall Hlt).
    destruct Hall as [a [b [c [Ha [Hb [Hc Hd]]]]]].
    rewrite Ha in H1. inversion H1. subst a.
    rewrite Hb in H2. inversion H2. subst b.
    rewrite Hc in H3. inversion H3. subst c.
    destruct Hd as [Hab _].
    apply Hab. reflexivity.
Qed.