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

Example test_is_happy_agbebfx: is_happy_spec ("agbebfx"%string) false.
Proof.
  right.
  split.
  - reflexivity.
  - unfold not; intros Hhappy.
    unfold happy_prop in Hhappy.
    destruct Hhappy as [Hlen Hall].
    assert (Hlt: 2 + 2 < String.length ("agbebfx"%string)) by (simpl; lia).
    specialize (Hall 2 Hlt).
    destruct Hall as [a [b [c [Ha2 [Hb3 [Hc4 Hd]]]]]].
    assert (Heq24 : nth_error_string ("agbebfx"%string) 2 = nth_error_string ("agbebfx"%string) 4).
    { simpl. reflexivity. }
    pose proof (eq_trans (eq_sym Ha2) (eq_trans Heq24 Hc4)) as Hac_eq.
    inversion Hac_eq; subst.
    destruct Hd as [_ [Hac _]].
    apply Hac.
    reflexivity.
Qed.