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

Example test_is_happy_LJzRm: is_happy_spec ("LJzRm"%string) true.
Proof.
  left.
  split.
  - reflexivity.
  - unfold happy_prop.
    split.
    + simpl. lia.
    + intros i Hi.
      destruct i as [|i1].
      * exists ("L"%char), ("J"%char), ("z"%char).
        repeat split; simpl; try reflexivity.
        unfold distinct3.
        repeat split.
        -- destruct (ascii_dec ("L"%char) ("J"%char)) as [Heq|Hneq]; [inversion Heq| exact Hneq].
        -- destruct (ascii_dec ("L"%char) ("z"%char)) as [Heq|Hneq]; [inversion Heq| exact Hneq].
        -- destruct (ascii_dec ("J"%char) ("z"%char)) as [Heq|Hneq]; [inversion Heq| exact Hneq].
      * destruct i1 as [|i2].
        -- exists ("J"%char), ("z"%char), ("R"%char).
           repeat split; simpl; try reflexivity.
           unfold distinct3.
           repeat split.
           ++ destruct (ascii_dec ("J"%char) ("z"%char)) as [Heq|Hneq]; [inversion Heq| exact Hneq].
           ++ destruct (ascii_dec ("J"%char) ("R"%char)) as [Heq|Hneq]; [inversion Heq| exact Hneq].
           ++ destruct (ascii_dec ("z"%char) ("R"%char)) as [Heq|Hneq]; [inversion Heq| exact Hneq].
        -- destruct i2 as [|i3].
           ++ exists ("z"%char), ("R"%char), ("m"%char).
              repeat split; simpl; try reflexivity.
              unfold distinct3.
              repeat split.
              ** destruct (ascii_dec ("z"%char) ("R"%char)) as [Heq|Hneq]; [inversion Heq| exact Hneq].
              ** destruct (ascii_dec ("z"%char) ("m"%char)) as [Heq|Hneq]; [inversion Heq| exact Hneq].
              ** destruct (ascii_dec ("R"%char) ("m"%char)) as [Heq|Hneq]; [inversion Heq| exact Hneq].
           ++ exfalso.
              simpl in Hi. lia.
Qed.