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

Definition big_s : string :=
  "abcdefghijklabcdefgabcdefgcdefgabcabaabcdefghijklmnopqrstuvwxyzabcdefghijklmnopqarstuvwxyzbabababababaaddbbccddeeaabbccddeeabababababababababababababababababdecfgabcabababababbabababababababababababababababababababdefgcdefgabcdefgrstuvwxyzabcdefghijklmnopqrsabcccaaabbddeeffftuvwxyz"%string.

Example test_is_happy_long: is_happy_spec big_s false.
Proof.
  right.
  split.
  - reflexivity.
  - unfold not; intros H.
    unfold happy_prop in H.
    destruct H as [Hlen Hall].
    set (i := 34).
    assert (Hlt : i + 2 < String.length big_s).
    { unfold big_s; simpl; lia. }
    specialize (Hall i Hlt).
    destruct Hall as [a [b [c [Ha [Hb [Hc Hdistinct]]]]]].
    subst i.
    unfold big_s in Ha, Hb, Hc.
    simpl in Ha.
    simpl in Hb.
    simpl in Hc.
    destruct Hdistinct as [_ [Hac _]].
    inversion Ha; subst.
    inversion Hc; subst.
    apply Hac; reflexivity.
Qed.