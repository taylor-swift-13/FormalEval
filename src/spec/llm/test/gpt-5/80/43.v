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

Example test_is_happy_space_this_is_baaacbacbbat: is_happy_spec (" this is baaacbacbbat"%string) false.
Proof.
  right.
  split.
  - reflexivity.
  - unfold not; intros H.
    unfold happy_prop in H.
    destruct H as [Hlen Hall].
    specialize (Hall 10).
    assert (Hbound: 10 + 2 < String.length (" this is baaacbacbbat"%string)) by (simpl; lia).
    specialize (Hall Hbound).
    destruct Hall as [a [b [c [Ha [Hb [Hc Hd]]]]]].
    assert (H10 : nth_error_string (" this is baaacbacbbat"%string) 10 = Some "a"%char) by reflexivity.
    assert (H11 : nth_error_string (" this is baaacbacbbat"%string) (10 + 1) = Some "a"%char) by reflexivity.
    assert (H12 : nth_error_string (" this is baaacbacbbat"%string) (10 + 2) = Some "a"%char) by reflexivity.
    rewrite H10 in Ha. inversion Ha; subst a.
    rewrite H11 in Hb. inversion Hb; subst b.
    rewrite H12 in Hc. inversion Hc; subst c.
    destruct Hd as [Hab _].
    apply Hab. reflexivity.
Qed.