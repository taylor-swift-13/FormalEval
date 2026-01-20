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

Example test_is_happy_puFerT: is_happy_spec ("puFerT"%string) true.
Proof.
  left.
  split.
  - reflexivity.
  - unfold happy_prop.
    split.
    + simpl. lia.
    + intros i Hi.
      destruct i as [|i1].
      * exists "p"%char, "u"%char, "F"%char.
        repeat split; simpl; try reflexivity.
        -- destruct (ascii_dec "p"%char "u"%char) as [Heq|Hneq]; [exfalso; inversion Heq; discriminate| exact Hneq].
        -- destruct (ascii_dec "p"%char "F"%char) as [Heq|Hneq]; [exfalso; inversion Heq; discriminate| exact Hneq].
        -- destruct (ascii_dec "u"%char "F"%char) as [Heq|Hneq]; [exfalso; inversion Heq; discriminate| exact Hneq].
      * destruct i1 as [|i2].
        -- exists "u"%char, "F"%char, "e"%char.
           repeat split; simpl; try reflexivity.
           ++ destruct (ascii_dec "u"%char "F"%char) as [Heq|Hneq]; [exfalso; inversion Heq; discriminate| exact Hneq].
           ++ destruct (ascii_dec "u"%char "e"%char) as [Heq|Hneq]; [exfalso; inversion Heq; discriminate| exact Hneq].
           ++ destruct (ascii_dec "F"%char "e"%char) as [Heq|Hneq]; [exfalso; inversion Heq; discriminate| exact Hneq].
        -- destruct i2 as [|i3].
           ** exists "F"%char, "e"%char, "r"%char.
              repeat split; simpl; try reflexivity.
              --- destruct (ascii_dec "F"%char "e"%char) as [Heq|Hneq]; [exfalso; inversion Heq; discriminate| exact Hneq].
              --- destruct (ascii_dec "F"%char "r"%char) as [Heq|Hneq]; [exfalso; inversion Heq; discriminate| exact Hneq].
              --- destruct (ascii_dec "e"%char "r"%char) as [Heq|Hneq]; [exfalso; inversion Heq; discriminate| exact Hneq].
           ** destruct i3 as [|i4].
              --- exists "e"%char, "r"%char, "T"%char.
                  repeat split; simpl; try reflexivity.
                  **** destruct (ascii_dec "e"%char "r"%char) as [Heq|Hneq]; [exfalso; inversion Heq; discriminate| exact Hneq].
                  **** destruct (ascii_dec "e"%char "T"%char) as [Heq|Hneq]; [exfalso; inversion Heq; discriminate| exact Hneq].
                  **** destruct (ascii_dec "r"%char "T"%char) as [Heq|Hneq]; [exfalso; inversion Heq; discriminate| exact Hneq].
              --- exfalso. simpl in Hi. lia.
Qed.