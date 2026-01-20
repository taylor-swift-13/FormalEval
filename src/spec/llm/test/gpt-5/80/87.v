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

Example test_is_happy_bRxtTU_this_is_baaacbaicbbate: is_happy_spec ("bRxtTU this is baaacbaicbbate"%string) false.
Proof.
  right.
  split.
  - reflexivity.
  - unfold not; intros H.
    unfold happy_prop in H.
    destruct H as [Hlen Hforall].
    assert (Hbound: 16 + 2 < String.length ("bRxtTU this is baaacbaicbbate"%string)).
    { simpl. lia. }
    pose proof (Hforall 16 Hbound) as Hspec.
    destruct Hspec as [a [b [c [E16 [E17 [E18 D]]]]]].
    assert (H16: nth_error_string ("bRxtTU this is baaacbaicbbate"%string) 16 = Some "a"%char).
    { simpl. reflexivity. }
    assert (H17: nth_error_string ("bRxtTU this is baaacbaicbbate"%string) (16 + 1) = Some "a"%char).
    { simpl. reflexivity. }
    assert (H18: nth_error_string ("bRxtTU this is baaacbaicbbate"%string) (16 + 2) = Some "a"%char).
    { simpl. reflexivity. }
    rewrite E16 in H16; inversion H16; subst a.
    rewrite E17 in H17; inversion H17; subst b.
    rewrite E18 in H18; inversion H18; subst c.
    destruct D as [Dab [Dac Dbc]].
    apply Dab.
    reflexivity.
Qed.