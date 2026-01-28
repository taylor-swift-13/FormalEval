Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.

Open Scope string_scope.

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

Example test_happy_complex : is_happy_spec " this is bacbacba comnnt" false.
Proof.
  unfold is_happy_spec.
  right.
  split.
  - reflexivity.
  - unfold happy_prop.
    intro H.
    destruct H as [_ H].
    specialize (H 20).
    assert (Hlen : 20 + 2 < String.length " this is bacbacba comnnt").
    { simpl. lia. }
    apply H in Hlen.
    destruct Hlen as [a [b [c [Ha [Hb [Hc Hdist]]]]]].
    simpl in Ha, Hb, Hc.
    inversion Ha; subst.
    inversion Hb; subst.
    inversion Hc; subst.
    destruct Hdist as [_ [_ Hcontra]].
    apply Hcontra.
    reflexivity.
Qed.