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

Example test_is_happy_spaces: is_happy_spec (" t his   thish i s b abatis bat"%string) false.
Proof.
  right.
  split.
  - reflexivity.
  - unfold not; intros Happ.
    unfold happy_prop in Happ.
    destruct Happ as [Hlen Hall].
    specialize (Hall 6).
    assert (6 + 2 < String.length (" t his   thish i s b abatis bat"%string)) as Hbound by (simpl; lia).
    specialize (Hall Hbound).
    destruct Hall as [a [b [c [Ha [Hb [Hc Hdistinct]]]]]].
    simpl in Ha.
    simpl in Hb.
    inversion Ha; subst a.
    inversion Hb; subst b.
    destruct Hdistinct as [Hab _].
    apply Hab; reflexivity.
Qed.