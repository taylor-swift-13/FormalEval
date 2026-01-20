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

Example test_is_happy_long_false: is_happy_spec ("abcbcabcabcabcabcabcabcabcabcabcabcabcaaaaabbbbccccdeeeddddcccaaeeeedddccccabcabcabbcabcabcababcab"%string) false.
Proof.
  right.
  split.
  - reflexivity.
  - unfold not; intros H.
    unfold happy_prop in H.
    destruct H as [Hlen Hall].
    specialize (Hall 38).
    assert (38 + 2 < String.length ("abcbcabcabcabcabcabcabcabcabcabcabcabcaaaaabbbbccccdeeeddddcccaaeeeedddccccabcabcabbcabcabcababcab"%string)) as Hlt.
    { simpl. lia. }
    specialize (Hall Hlt).
    destruct Hall as [a [b [c [Ha [Hb [Hc Hdist]]]]]].
    simpl in Ha.
    simpl in Hb.
    inversion Ha; subst.
    inversion Hb; subst.
    destruct Hdist as [Hneq _].
    apply Hneq. reflexivity.
Qed.