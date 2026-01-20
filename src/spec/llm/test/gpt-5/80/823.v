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

Example test_is_happy_DsrQgZMOa: is_happy_spec ("DsrQgZMOa"%string) true.
Proof.
  left.
  split.
  - reflexivity.
  - unfold happy_prop.
    split.
    + simpl. lia.
    + intros i Hi.
      destruct i as [|i1].
      * repeat eexists.
        repeat split; simpl; try reflexivity.
        unfold distinct3.
        repeat split.
        -- destruct (ascii_dec "D"%char "s"%char) as [Heq|Hneq]; [inversion Heq|exact Hneq].
        -- destruct (ascii_dec "D"%char "r"%char) as [Heq|Hneq]; [inversion Heq|exact Hneq].
        -- destruct (ascii_dec "s"%char "r"%char) as [Heq|Hneq]; [inversion Heq|exact Hneq].
      * destruct i1 as [|i2].
        -- repeat eexists.
           repeat split; simpl; try reflexivity.
           unfold distinct3.
           repeat split.
           ++ destruct (ascii_dec "s"%char "r"%char) as [Heq|Hneq]; [inversion Heq|exact Hneq].
           ++ destruct (ascii_dec "s"%char "Q"%char) as [Heq|Hneq]; [inversion Heq|exact Hneq].
           ++ destruct (ascii_dec "r"%char "Q"%char) as [Heq|Hneq]; [inversion Heq|exact Hneq].
        -- destruct i2 as [|i3].
           ** repeat eexists.
              repeat split; simpl; try reflexivity.
              unfold distinct3.
              repeat split.
              --- destruct (ascii_dec "r"%char "Q"%char) as [Heq|Hneq]; [inversion Heq|exact Hneq].
              --- destruct (ascii_dec "r"%char "g"%char) as [Heq|Hneq]; [inversion Heq|exact Hneq].
              --- destruct (ascii_dec "Q"%char "g"%char) as [Heq|Hneq]; [inversion Heq|exact Hneq].
           ** destruct i3 as [|i4].
              --- repeat eexists.
                  repeat split; simpl; try reflexivity.
                  unfold distinct3.
                  repeat split.
                  ---- destruct (ascii_dec "Q"%char "g"%char) as [Heq|Hneq]; [inversion Heq|exact Hneq].
                  ---- destruct (ascii_dec "Q"%char "Z"%char) as [Heq|Hneq]; [inversion Heq|exact Hneq].
                  ---- destruct (ascii_dec "g"%char "Z"%char) as [Heq|Hneq]; [inversion Heq|exact Hneq].
              --- destruct i4 as [|i5].
                  ---- repeat eexists.
                       repeat split; simpl; try reflexivity.
                       unfold distinct3.
                       repeat split.
                       ----- destruct (ascii_dec "g"%char "Z"%char) as [Heq|Hneq]; [inversion Heq|exact Hneq].
                       ----- destruct (ascii_dec "g"%char "M"%char) as [Heq|Hneq]; [inversion Heq|exact Hneq].
                       ----- destruct (ascii_dec "Z"%char "M"%char) as [Heq|Hneq]; [inversion Heq|exact Hneq].
                  ---- destruct i5 as [|i6].
                       ----- repeat eexists.
                             repeat split; simpl; try reflexivity.
                             unfold distinct3.
                             repeat split.
                             ------ destruct (ascii_dec "Z"%char "M"%char) as [Heq|Hneq]; [inversion Heq|exact Hneq].
                             ------ destruct (ascii_dec "Z"%char "O"%char) as [Heq|Hneq]; [inversion Heq|exact Hneq].
                             ------ destruct (ascii_dec "M"%char "O"%char) as [Heq|Hneq]; [inversion Heq|exact Hneq].
                       ----- destruct i6 as [|i7].
                             ------ repeat eexists.
                                   repeat split; simpl; try reflexivity.
                                   unfold distinct3.
                                   repeat split.
                                   ------- destruct (ascii_dec "M"%char "O"%char) as [Heq|Hneq]; [inversion Heq|exact Hneq].
                                   ------- destruct (ascii_dec "M"%char "a"%char) as [Heq|Hneq]; [inversion Heq|exact Hneq].
                                   ------- destruct (ascii_dec "O"%char "a"%char) as [Heq|Hneq]; [inversion Heq|exact Hneq].
                             ------ exfalso. simpl in Hi. lia.
Qed.