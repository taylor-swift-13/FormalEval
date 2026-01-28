Require Import ZArith Lia Znumtheory.
Open Scope Z_scope.

(* Pre: at least one of `a` or `b` is non-zero (gcd(0,0) is undefined) *)
Definition problem_13_pre (a b : Z) : Prop :=
  a <> 0 \/ b <> 0.

(* Provided (but incorrect) spec *)
Definition problem_13_spec (a b output : Z) : Prop :=
  (output mod a = 0) /\
  (output mod b = 0) /\
  (forall x : Z, (x mod a = 0) -> (x mod b = 0) -> x > 0 -> x <= output).

(* Corrected spec, matching the description:
   Return a greatest common divisor of two integers a and b *)
Definition problem_13_spec_correct (a b output : Z) : Prop :=
  (a mod output = 0) /\
  (b mod output = 0) /\
  (forall x : Z, (a mod x = 0) -> (b mod x = 0) -> x > 0 -> x <= output).

(* Test case: input = [3%Z; 7%Z], output = 1%Z *)

Example problem_13_testcase_pre : problem_13_pre 3%Z 7%Z.
Proof.
left. lia.
Qed.

(* Show that the provided (incorrect) spec does NOT hold for the test case *)
Example problem_13_spec_incorrect_fails : ~ problem_13_spec 3%Z 7%Z 1%Z.
Proof.
intros H.
destruct H as [Hmod3 [Hmod7 _]].
assert (H13 : 1 mod 3 = 1).
{ apply Z.mod_small; lia. }
rewrite H13 in Hmod3.
lia.
Qed.

(* Prove the corrected spec holds for the test case *)
Example problem_13_spec_correct_example : problem_13_spec_correct 3%Z 7%Z 1%Z.
Proof.
unfold problem_13_spec_correct.
split.
- (* 3 mod 1 = 0 *)
  compute; reflexivity.
- split.
  + (* 7 mod 1 = 0 *)
    compute; reflexivity.
  + (* Any positive common divisor of 3 and 7 is <= 1 *)
    intros x Hx3 Hx7 Hxpos.
    assert (Hxnonzero : x <> 0) by lia.
    pose proof (Zmod_divide _ _ Hxnonzero Hx3) as [p Hp]. (* 3 = x * p or p * x depending on lemma orientation *)
    pose proof (Zmod_divide _ _ Hxnonzero Hx7) as [q Hq]. (* 7 = x * q or q * x *)
    assert (Hcomb : 5 * 3 + (-2) * 7 = 1) by (compute; reflexivity).
    (* Rewrite 3 and 7 using divisibility by x *)
    rewrite Hp, Hq in Hcomb.
    (* We now have 5 * (p * x) + (-2) * (q * x) = 1 or with x on left; normalize to have x on the right *)
    repeat rewrite Z.mul_assoc in Hcomb.
    (* (5 * p) * x + ((-2) * q) * x = 1 *)
    rewrite <- Z.mul_add_distr_r in Hcomb.
    (* ((5 * p) + ((-2) * q)) * x = 1 *)
    (* Commute to get x * (...) = 1 *)
    rewrite Z.mul_comm in Hcomb.
    (* x * ((5 * p) + ((-2) * q)) = 1 *)
    assert (Hdiv1 : Z.divide x 1).
    { exists ((5 * p) + (-2) * q).
      apply eq_sym.
      exact Hcomb.
    }
    apply Zdivide_1 in Hdiv1.
    destruct Hdiv1 as [-> | ->]; lia.
Qed.