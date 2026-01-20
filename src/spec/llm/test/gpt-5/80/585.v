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

Example test_is_happy_adddaaaabbbbccccddddbccccdddd: is_happy_spec ("adddaaaabbbbccccddddbccccdddd"%string) false.
Proof.
  right.
  split.
  - reflexivity.
  - unfold not; intros H.
    unfold happy_prop in H.
    destruct H as [Hlen Hall].
    specialize (Hall 1).
    assert (Hlt: 1 + 2 < String.length ("adddaaaabbbbccccddddbccccdddd"%string)) by (simpl; lia).
    specialize (Hall Hlt).
    destruct Hall as [a [b [c [H1 [H2 [H3 Hdist]]]]]].
    assert (Heq12: nth_error_string ("adddaaaabbbbccccddddbccccdddd"%string) 1 =
                   nth_error_string ("adddaaaabbbbccccddddbccccdddd"%string) (1 + 1)).
    { simpl; reflexivity. }
    rewrite H1 in Heq12.
    rewrite H2 in Heq12.
    injection Heq12 as Hab_eq.
    destruct Hdist as [Hab [Hac Hbc]].
    apply Hab.
    exact Hab_eq.
Qed.