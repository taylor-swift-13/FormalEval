Require Import Coq.Arith.Arith Coq.Bool.Bool Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.

Inductive digit_7_count_rel : nat -> nat -> Prop :=
| d7c_zero : digit_7_count_rel 0 0
| d7c_mod10_7 : forall n c,
    n mod 10 = 7 ->
    digit_7_count_rel (n / 10) c ->
    digit_7_count_rel n (S c)
| d7c_mod10_other : forall n c,
    n mod 10 <> 7 ->
    digit_7_count_rel (n / 10) c ->
    digit_7_count_rel n c.

Inductive fizz_buzz_rel : nat -> nat -> Prop :=
| fbz_zero : fizz_buzz_rel 0 0
| fbz_next_div : forall n acc c,
    fizz_buzz_rel n acc ->
    (n mod 11 = 0 \/ n mod 13 = 0) ->
    digit_7_count_rel n c ->
    fizz_buzz_rel (S n) (acc + c)
| fbz_next_nodiv : forall n acc,
    fizz_buzz_rel n acc ->
    ~(n mod 11 = 0 \/ n mod 13 = 0) ->
    fizz_buzz_rel (S n) acc.

Definition problem_36_pre (n : nat) : Prop := True.

Definition problem_36_spec (n : nat) (output : nat) : Prop :=
  fizz_buzz_rel n output.

(* Helper lemma: digit_7_count_rel for numbers with no digit 7 is zero *)
Lemma digit_7_count_no_7 :
  forall n,
  (forall d, (n / Nat.pow 10 d) mod 10 <> 7) ->
  digit_7_count_rel n 0.
Proof.
  induction n using lt_wf_ind.
  intros Hno7.
  destruct n.
  - constructor.
  - assert (n / 10 < S n) by (apply Nat.div_lt; lia).
    specialize (H0 (n / 10) H).
    pose proof (Nat.mod_upper_bound n 10) as HM; try lia.
    destruct (Nat.eq_dec (n mod 10) 7) as [Heq7 | Hneq7].
    + exfalso.
      specialize (H0 0).
      rewrite Nat.pow_0_r in H0.
      simpl in H0.
      apply H0.
      assumption.
    + apply d7c_mod10_other.
      * assumption.
      * apply H0.
        intros d.
        specialize (H (S d)).
        rewrite Nat.pow_succ_r' in H by lia.
        rewrite Nat.div_div in H by lia.
        apply H.
Qed.

(* List of numbers < 50 divisible by 11 or 13 *)
Definition div11or13_lt50 : list nat := [11; 13; 22; 26; 33; 39; 44].

(* Lemma: All numbers in div11or13_lt50 have digit_7_count_rel x 0 *)
Lemma digit_7_count_div11or13_zero :
  forall x, In x div11or13_lt50 -> digit_7_count_rel x 0.
Proof.
  intros x Hin.
  (* Each of these numbers contains no digit 7 *)
  apply digit_7_count_no_7.
  intros d.
  destruct x eqn:Ex; try discriminate.
  destruct x eqn:Ex2; try discriminate.
  destruct x eqn:Ex3; try discriminate.
  destruct x eqn:Ex4; try discriminate.
  destruct x eqn:Ex5; try discriminate.
  destruct x eqn:Ex6; try discriminate.
  destruct x eqn:Ex7; try discriminate.
  destruct x eqn:Ex8; try discriminate.

  (* Instead of using the eqn, just analyze digits:

     11: digits 1 and 1
     13: digits 1 and 3
     22: digits 2 and 2
     26: digits 2 and 6
     33: digits 3 and 3
     39: digits 3 and 9
     44: digits 4 and 4

  None contain digit 7
  *)
  (* So prove for all d, digit is not 7 *)
  intros d0.
  unfold div11or13_lt50 in Hin.
  simpl in Hin.
  destruct Hin as [Hx|Hin].
  - subst x.
    (* For each number, prove the digit not 7 *)
    destruct d0.
    + (* ones digit *)
      all: try discriminate.
      all: simpl; repeat (rewrite Nat.div_1_r);
        try (simpl; lia).
      all: match goal with
           | |- ?n mod 10 <> 7 => compute; congruence
           end.
    + (* tens digit *)
      all: try discriminate.
      all: repeat rewrite Nat.pow_1_r.
      all: try (simpl; lia).
      all: match goal with
           | |- (n / 10) mod 10 <> 7 => compute; congruence
           end.
  - destruct Hin as [H13|Hin].
    + subst x.
      intros d0.
      destruct d0; simpl; compute; congruence.
    + destruct Hin as [H22|Hin].
      * subst x.
        intros d0.
        destruct d0; simpl; compute; congruence.
      * destruct Hin as [H26|Hin].
        -- subst x.
           intros d0.
           destruct d0; simpl; compute; congruence.
        -- destruct Hin as [H33|Hin].
           ++ subst x.
              intros d0.
              destruct d0; simpl; compute; congruence.
           ++ destruct Hin as [H39|Hin].
              ** subst x.
                 intros d0.
                 destruct d0; simpl; compute; congruence.
              ** destruct Hin as [H44|Hnil].
                 --- subst x.
                     intros d0.
                     destruct d0; simpl; compute; congruence.
                 --- contradiction.
Qed.

(* The main example proof *)
Example fizz_buzz_50_0 : fizz_buzz_rel 50 0.
Proof.
  (* We'll prove by induction on n: fizz_buzz_rel n acc with acc=0,
     when all divisible numbers less than n have digit_7_count_rel x 0 *)

  assert (H :
    forall n acc,
      n <= 50 ->
      fizz_buzz_rel n acc ->
      (forall x, x < n -> (x mod 11 = 0 \/ x mod 13 = 0) -> digit_7_count_rel x 0) ->
      acc = 0).
  {
    induction n using lt_wf_ind.
    intros acc Hle Hfbz Hdigit.
    destruct n.
    - inversion Hfbz; subst. reflexivity.
    - inversion Hfbz; subst.
      + (* divisible case *)
        specialize (H (acc0) (le_n n) H2 Hdigit).
        rewrite H.
        specialize (Hdigit n).
        assert (n < S n) by lia.
        specialize (Hdigit H0 H1).
        inversion Hdigit; subst.
        simpl. lia.
      + (* not divisible case *)
        specialize (H n acc0 (Lt.lt_lt_succ_r _ _ Hle) H2 Hdigit).
        lia.
  }

  apply (H 50 0).
  - lia.
  - apply fbz_zero.
  - intros x Hlt Hdiv.
    apply digit_7_count_div11or13_zero.
    (* Prove x ∈ div11or13_lt50 from assumptions *)
    unfold div11or13_lt50.
    simpl.
    (* x divisible by 11 or 13 and less than 50 means x is in the list *)
    assert (Hlist: In x [11;13;22;26;33;39;44]).
    {
      (* Use divisibility and bound *)
      destruct Hdiv.
      + (* divisible by 11 *)
        remember (x / 11) as k eqn:Hk.
        assert (x = 11 * k) by (subst; apply Nat.div_exact; lia).
        subst x.
        assert (k * 11 < 50) by lia.
        assert (k <= 4) by lia.
        destruct k; simpl; try lia.
        * left; reflexivity.
        * right; left; reflexivity.
        * right; right; left; reflexivity.
        * right; right; right; left; reflexivity.
        * right; right; right; right; reflexivity.
      + (* divisible by 13 *)
        remember (x / 13) as k eqn:Hk.
        assert (x = 13 * k) by (subst; apply Nat.div_exact; lia).
        subst x.
        assert (k * 13 < 50) by lia.
        assert (k <= 3) by lia.
        destruct k; simpl; try lia.
        * left; reflexivity.
        * right; left; reflexivity.
        * right; right; left; reflexivity.
        * right; right; right; reflexivity.
    }
    assumption.
Qed.