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

Lemma nth_error_string_Some_lt: forall s n ch, nth_error_string s n = Some ch -> n < String.length s.
Proof.
  induction s; intros n ch H; destruct n; simpl in *; try discriminate; simpl.
  - inversion H; subst; simpl; lia.
  - apply IHs in H. simpl. lia.
Qed.

Definition big_string := ("abcccaaa11223344556677889900112233445566778899001122334455667abcabccddd4daaaabbbbccccddddaaaabbbbccccddddcabcabcabcabcabcabcabaaddbbccdcdeeaabbccddeebcab7889900bbddeefff"%string).

Example test_is_happy_new: is_happy_spec big_string false.
Proof.
  right.
  split.
  - reflexivity.
  - unfold not; intros H.
    unfold happy_prop in H.
    destruct H as [Hlen Hall].
    assert (Hpre: 2 + 2 < String.length big_string).
    { assert (Hsome: nth_error_string big_string 4 = Some "c"%char) by (simpl; reflexivity).
      apply nth_error_string_Some_lt in Hsome.
      lia.
    }
    specialize (Hall 2).
    specialize (Hall Hpre).
    destruct Hall as [a [b [c [Ha [Hb [Hc Hdistinct]]]]]].
    simpl in Ha, Hb, Hc.
    inversion Ha; subst.
    inversion Hb; subst.
    inversion Hc; subst.
    destruct Hdistinct as [Hab _].
    apply Hab; reflexivity.
Qed.