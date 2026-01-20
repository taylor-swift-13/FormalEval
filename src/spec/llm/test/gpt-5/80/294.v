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

Example test_is_happy_single_a: is_happy_spec ("abcdefgabcdefgcdefgabcdefgabcdefgcdeqwerty112233445566775565677889900uiopasdfghjklzxcvbnmqwertyuiopasdfghjklzxcvbfgabcdefg"%string) false.
Proof.
  right.
  split.
  - reflexivity.
  - unfold not; intros H.
    unfold happy_prop in H.
    destruct H as [Hlen Hall].
    remember ("abcdefgabcdefgcdefgabcdefgabcdefgcdeqwerty"%string) as pre.
    remember ("abcdefgabcdefgcdefgabcdefgabcdefgcdeqwerty112233445566775565677889900uiopasdfghjklzxcvbnmqwertyuiopasdfghjklzxcvbfgabcdefg"%string) as s.
    pose (i := String.length pre).
    assert (Hi : i + 2 < String.length s).
    { unfold i; subst pre; subst s; simpl; lia. }
    specialize (Hall i).
    assert (Hexists := Hall Hi).
    clear Hall.
    destruct Hexists as [a [b [c [Ha [Hb [Hc Hd]]]]]].
    assert (H0 : nth_error_string s i = Some ("1"%char)).
    { subst s; unfold i; subst pre; simpl; reflexivity. }
    assert (H1 : nth_error_string s (i + 1) = Some ("1"%char)).
    { subst s; unfold i; subst pre; simpl; reflexivity. }
    assert (H2 : nth_error_string s (i + 2) = Some ("2"%char)).
    { subst s; unfold i; subst pre; simpl; reflexivity. }
    rewrite H0 in Ha; inversion Ha; subst a; clear Ha.
    rewrite H1 in Hb; inversion Hb; subst b; clear Hb.
    rewrite H2 in Hc; inversion Hc; subst c; clear Hc.
    unfold distinct3 in Hd.
    destruct Hd as [Hab [Hac Hbc]].
    apply Hab; reflexivity.
Qed.