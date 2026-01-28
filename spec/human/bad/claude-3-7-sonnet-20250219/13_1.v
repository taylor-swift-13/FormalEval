Require Import ZArith.
Open Scope Z_scope.
Require Import Lia.

(* Pre: at least one of `a` or `b` is non-zero (gcd(0,0) is undefined) *)
Definition problem_13_pre (a b : Z) : Prop :=
  a <> 0 \/ b <> 0.

(* Specification as stated:
   output divides a and b means a mod output = 0 and b mod output = 0,
   and output is greatest such positive divisor *)
Definition problem_13_spec (a b output : Z) : Prop :=
  (a mod output = 0) /\
  (b mod output = 0) /\
  (forall x : Z, x > 0 -> (a mod x = 0) -> (b mod x = 0) -> x <= output).

(* Test case with input 3 and 7, output 1 *)
Example test_gcd_3_7:
  problem_13_spec 3 7 1.
Proof.
  unfold problem_13_spec.
  repeat split.
  - rewrite Z.mod_1_l; lia.
  - rewrite Z.mod_1_l; lia.
  - intros x Hxpos Hxdiva Hxdivb.
    (* Show that any positive x dividing 3 and 7 satisfies x ≤ 1 *)
    (* Use that gcd(3,7)=1 and any common divisor divides gcd *)

    (* Convert mod divides to Z.divide *)
    apply Z.mod_divide in Hxdiva; try lia.
    apply Z.mod_divide in Hxdivb; try lia.

    (* x divides 3 and 7 *)
    assert (Z.divide x (Z.gcd 3 7)).
    { apply Z.divide_gcd; assumption. }

    (* gcd(3,7) = 1 *)
    rewrite Z.gcd_comm.
    assert (Z.gcd 3 7 = 1) as Hgcd by reflexivity.
    rewrite Hgcd in H.

    (* So x divides 1 *)
    unfold Z.divide in H.
    destruct H as [k Hk].
    (* x * k = 1 *)
    assert (x > 0) by exact Hxpos.

    (* Over integers, if positive x and x * k = 1, then x = 1 and k = 1 *)
    apply (Z.mul_eq_1_pos x k) in Hk; auto.
    destruct Hk as [Hx1 _].
    subst x.
    lia.
Qed.