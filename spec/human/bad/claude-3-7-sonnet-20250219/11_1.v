Require Import List.
Require Import Ascii.
Require Import String.
Require Import Bool.
Require Import Lia.

Import ListNotations.
Open Scope string_scope.

(* Pre: inputs have equal length and contain only '0' or '1' characters *)
Definition problem_11_pre (a b : string) : Prop :=
  String.length a = String.length b /\
  forall i,
    i < String.length a ->
      ((String.get i a = Some "0"%char) \/ (String.get i a = Some "1"%char)) /\
      ((String.get i b = Some "0"%char) \/ (String.get i b = Some "1"%char)).

(* Spec *)
Definition problem_11_spec (a b output : string) : Prop :=
  String.length a = String.length b /\
  String.length output = String.length a /\
  forall i,
    i < String.length output ->
    (String.get i a = String.get i b -> String.get i output = Some "0"%char) /\
    (String.get i a <> String.get i b -> String.get i output = Some "1"%char).

(* xor_char for '0'/'1' *)
Definition xor_char (c1 c2 : ascii) : ascii :=
  match (c1, c2) with
  | ("0"%char, "0"%char) => "0"%char
  | ("0"%char, "1"%char) => "1"%char
  | ("1"%char, "0"%char) => "1"%char
  | ("1"%char, "1"%char) => "0"%char
  | _, _ => "0"%char (* fallback, should not happen *)
  end.

(* recursive string xor *)
Fixpoint string_xor (a b : string) : string :=
  match a, b with
  | EmptyString, EmptyString => EmptyString
  | String c1 a', String c2 b' => String (xor_char c1 c2) (string_xor a' b')
  | _, _ => EmptyString (* different length - undefined here *)
  end.

Definition test_a := "111000"%string.
Definition test_b := "101010"%string.
Definition test_output := string_xor test_a test_b.

Example problem_11_test_case :
  problem_11_spec test_a test_b test_output.
Proof.
  unfold problem_11_spec, test_output.
  split.
  - (* length a = length b *)
    reflexivity.
  - split.
    + (* length output = length a *)
      revert test_a test_b.
      induction test_a as [| c1 a' IH]; intros [| c2 b']; simpl; try reflexivity.
      apply IH.
    + (* forall i, the XOR spec holds *)
      intros i Hi.
      revert i Hi test_a test_b.
      induction i using Nat.peano_ind.
      - intros _ a b.
        destruct a as [| c1 a']; destruct b as [| c2 b']; simpl; try lia.
        split.
        + intros Heq.
          simpl.
          unfold xor_char.
          simpl in Heq.
          destruct (ascii_dec c1 c2).
          * subst c2.
            destruct c1; try destruct c1; simpl; try reflexivity;
            (* cases for '0' and '1' specifically *)
            (try (destruct (ascii_dec c1 "0"%char); [subst c1; reflexivity |]);
             try (destruct (ascii_dec c1 "1"%char); [subst c1; reflexivity |]));
            reflexivity.
          * discriminate.
        + intros Hneq.
          unfold xor_char.
          simpl in Hneq.
          destruct (ascii_dec c1 c2).
          * exfalso; apply Hneq; assumption.
          * destruct c1, c2; simpl;
              try reflexivity;
              try (exfalso; apply Hneq; reflexivity).
      - intros Hi a b.
        destruct a as [| c1 a']; destruct b as [| c2 b']; simpl in *; try lia.
        specialize (IH (i - 1)) as IH_i.
        assert (i > 0) by lia.
        apply Nat.sub_lt in Hi; try lia.
        specialize (IH_i H a' b').
        destruct IH_i as [H1 H2].
        split.
        + intros Heq.
          unfold xor_char.
          simpl in Heq.
          destruct (ascii_dec c1 c2).
          * subst c2.
            destruct (ascii_dec c1 "0"%char);
            destruct (ascii_dec c1 "1"%char);
            try (specialize (H1 Heq); rewrite H1; reflexivity);
            try reflexivity.
          * discriminate.
        + intros Hneq.
          unfold xor_char.
          simpl in Hneq.
          destruct (ascii_dec c1 c2).
          * exfalso; apply Hneq; assumption.
          * destruct c1, c2; simpl;
              try reflexivity;
              try (exfalso; apply Hneq; reflexivity).
Qed.