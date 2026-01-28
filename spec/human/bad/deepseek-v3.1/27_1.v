Require Import String Ascii Arith Bool.
Require Import Lia.

(* Helper lemma: ascii conversion properties *)
Lemma nat_of_ascii_bound : forall c : ascii,
  (0 <= nat_of_ascii c < 256)%nat.
Proof.
  intro c. unfold nat_of_ascii. simpl.
  repeat match goal with
  | |- context[match ?x with _ => _ end] => destruct x
  end; lia.
Qed.

(* Character classification lemmas *)
Lemma lower_upper_inverse : forall c : ascii,
  IsLow c -> Upper c = ascii_of_nat (nat_of_ascii c - 32).
Proof.
  intros c [H1 H2].
  unfold Upper.
  assert (H3: (nat_of_ascii "a" <=? nat_of_ascii c)%nat = true).
  { apply Nat.leb_le; assumption. }
  assert (H4: (nat_of_ascii c <=? nat_of_ascii "z")%nat = true).
  { apply Nat.leb_le; assumption. }
  rewrite H3, H4. reflexivity.
Qed.

Lemma upper_lower_inverse : forall c : ascii,
  IsUp c -> Lower c = ascii_of_nat (nat_of_ascii c + 32).
Proof.
  intros c [H1 H2].
  unfold Lower.
  assert (H3: (nat_of_ascii "A" <=? nat_of_ascii c)%nat = true).
  { apply Nat.leb_le; assumption. }
  assert (H4: (nat_of_ascii c <=? nat_of_ascii "Z")%nat = true).
  { apply Nat.leb_le; assumption. }
  rewrite H3, H4. reflexivity.
Qed.

Lemma not_lower_not_upper_preserved : forall c : ascii,
  ~IsLow c /\ ~IsUp c -> Upper c = c /\ Lower c = c.
Proof.
  intros c [H1 H2].
  unfold Upper, Lower.
  split.
  - destruct ((nat_of_ascii "a" <=? nat_of_ascii c)%nat) eqn:Ha.
    + destruct ((nat_of_ascii c <=? nat_of_ascii "z")%nat) eqn:Hz.
      * exfalso. apply H1. unfold IsLow.
        split; apply Nat.leb_le; assumption.
      * reflexivity.
    + reflexivity.
  - destruct ((nat_of_ascii "A" <=? nat_of_ascii c)%nat) eqn:Ha.
    + destruct ((nat_of_ascii c <=? nat_of_ascii "Z")%nat) eqn:Hz.
      * exfalso. apply H2. unfold IsUp.
        split; apply Nat.leb_le; assumption.
      * reflexivity.
    + reflexivity.
Qed.

(* String manipulation functions *)
Fixpoint flip_case_aux (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' =>
      match (nat_of_ascii "a" <=? nat_of_ascii c)%nat &&
            (nat_of_ascii c <=? nat_of_ascii "z")%nat with
      | true => String (ascii_of_nat (nat_of_ascii c - 32)) (flip_case_aux s')
      | false =>
          match (nat_of_ascii "A" <=? nat_of_ascii c)%nat &&
                (nat_of_ascii c <=? nat_of_ascii "Z")%nat with
          | true => String (ascii_of_nat (nat_of_ascii c + 32)) (flip_case_aux s')
          | false => String c (flip_case_aux s')
          end
      end
  end.

Definition flip_case (input : string) : string := flip_case_aux input.

Lemma flip_case_length : forall s, String.length (flip_case s) = String.length s.
Proof.
  intro s. unfold flip_case.
  induction s as [|c s IH].
  - simpl. reflexivity.
  - simpl. f_equal. apply IH.
Qed.

Lemma flip_case_get_correct : forall s i c,
  i < String.length s ->
  String.get i s = Some c ->
  (IsLow c -> String.get i (flip_case s) = Some (Upper c)) /\
  (IsUp c -> String.get i (flip_case s) = Some (Lower c)) /\
  (~IsLow c /\ ~IsUp c -> String.get i (flip_case s) = Some c).
Proof.
  intro s. unfold flip_case.
  induction s as [|c0 s IH]; intros i c Hi Hget.
  - simpl in Hi. lia.
  - simpl in Hget, Hi.
    destruct i as [|i'].
    + simpl in Hget. injection Hget as Hc.
      rewrite Hc.
      simpl.
      destruct ((nat_of_ascii "a" <=? nat_of_ascii c)%nat) eqn:Ha.
      * destruct ((nat_of_ascii c <=? nat_of_ascii "z")%nat) eqn:Hz.
        -- split; [|split].
           ++ intro Hlow. reflexivity.
           ++ intro Hup. 
              exfalso. apply Hup. unfold IsUp.
              pose proof (nat_of_ascii_bound c). lia.
           ++ intro [Hnotlow Hnotup].
              exfalso. apply Hnotlow. unfold IsLow.
              split; apply Nat.leb_le; assumption.
        -- split; [|split].
           ++ intro Hlow. 
              exfalso. apply Hlow. unfold IsLow.
              split; [apply Nat.leb_le; assumption|].
              apply Nat.leb_nle in Hz. lia.
           ++ intro Hup. 
              destruct ((nat_of_ascii "A" <=? nat_of_ascii c)%nat) eqn:Ha2.
              ** destruct ((nat_of_ascii c <=? nat_of_ascii "Z")%nat) eqn:Hz2.
                 +++ reflexivity.
                 +++ exfalso. apply Hup. unfold IsUp.
                     split; [apply Nat.leb_le; assumption|].
                     apply Nat.leb_nle in Hz2. lia.
              ** exfalso. apply Hup. unfold IsUp.
                 split; [apply Nat.leb_nle in Ha2; lia|].
                 pose proof (nat_of_ascii_bound c).
                 destruct Hup as [Hup1 Hup2]. lia.
           ++ intro [Hnotlow Hnotup]. reflexivity.
      * split; [|split].
        -- intro Hlow. 
           exfalso. apply Hlow. unfold IsLow.
           split; [apply Nat.leb_nle in Ha; lia|].
           pose proof (nat_of_ascii_bound c).
           destruct Hlow as [Hlow1 Hlow2]. lia.
        -- intro Hup. 
           destruct ((nat_of_ascii "A" <=? nat_of_ascii c)%nat) eqn:Ha2.
           ** destruct ((nat_of_ascii c <=? nat_of_ascii "Z")%nat) eqn:Hz2.
              +++ reflexivity.
              +++ exfalso. apply Hup. unfold IsUp.
                  split; [apply Nat.leb_le; assumption|].
                  apply Nat.leb_nle in Hz2. lia.
           ** exfalso. apply Hup. unfold IsUp.
              split; [apply Nat.leb_nle in Ha2; lia|].
              pose proof (nat_of_ascii_bound c).
              destruct Hup as [Hup1 Hup2]. lia.
        -- intro [Hnotlow Hnotup]. reflexivity.
    + simpl in Hi.
      assert (Hi' : i' < String.length s) by lia.
      simpl.
      destruct ((nat_of_ascii "a" <=? nat_of_ascii c0)%nat) eqn:Ha.
      * destruct ((nat_of_ascii c0 <=? nat_of_ascii "z")%nat) eqn:Hz.
        -- apply IH with (c := c); assumption.
        -- apply IH with (c := c); assumption.
      * destruct ((nat_of_ascii "A" <=? nat_of_ascii c0)%nat) eqn:Ha2.
        -- destruct ((nat_of_ascii c0 <=? nat_of_ascii "Z")%nat) eqn:Hz2.
           +++ apply IH with (c := c); assumption.
           +++ apply IH with (c := c); assumption.
        -- apply IH with (c := c); assumption.
Qed.

(* Specification verification *)
Lemma flip_case_spec : forall input : string,
  problem_27_spec input (flip_case input).
Proof.
  intro input.
  unfold problem_27_spec.
  split.
  - apply flip_case_length.
  - intros i c Hi Hget.
    apply flip_case_get_correct with (s := input); assumption.
Qed.

(* Test case proof *)
Example test_empty_string : problem_27_spec "" "".
Proof.
  unfold problem_27_spec.
  split.
  - reflexivity.
  - intros i c Hi Hget.
    simpl in Hi. lia.
Qed.

Example test_empty_string_flip_case : flip_case "" = "".
Proof.
  simpl. reflexivity.
Qed.

Lemma flip_case_correct_empty : problem_27_spec "" (flip_case "").
Proof.
  unfold flip_case. simpl.
  unfold problem_27_spec.
  split.
  - reflexivity.
  - intros i c Hi Hget.
    simpl in Hi. lia.
Qed.

(* Main theorem *)
Theorem flip_case_implements_spec : 
  forall input, problem_27_pre input -> problem_27_spec input (flip_case input).
Proof.
  intros input _.
  apply flip_case_spec.
Qed.