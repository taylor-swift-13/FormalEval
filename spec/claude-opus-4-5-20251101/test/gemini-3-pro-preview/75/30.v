Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.

Open Scope Z_scope.

(* --- Specification Definitions --- *)

Definition is_prime (n : Z) : Prop :=
  n > 1 /\ forall d : Z, 1 < d < n -> Z.rem n d <> 0.

Inductive prime_factorization : Z -> list Z -> Prop :=
  | pf_one : prime_factorization 1 []
  | pf_cons : forall n p rest,
      n > 1 ->
      is_prime p ->
      Z.rem n p = 0 ->
      prime_factorization (Z.div n p) rest ->
      prime_factorization n (p :: rest).

Definition is_multiply_prime_spec (a : Z) (result : bool) : Prop :=
  (result = true <->
    (a > 1 /\
     exists p1 p2 p3 : Z,
       is_prime p1 /\ is_prime p2 /\ is_prime p3 /\
       a = p1 * p2 * p3)) /\
  (result = false <->
    (a <= 1 \/
     ~(exists p1 p2 p3 : Z,
         is_prime p1 /\ is_prime p2 /\ is_prime p3 /\
         a = p1 * p2 * p3))).

(* --- Test Case Proof --- *)

Example test_case_23 : is_multiply_prime_spec 23 false.
Proof.
  unfold is_multiply_prime_spec.
  split.
  - (* Case: false = true <-> ... *)
    split.
    + intro H. discriminate H.
    + intro H.
      destruct H as [_ [p1 [p2 [p3 [Hp1 [Hp2 [Hp3 Heq]]]]]]].
      destruct Hp1 as [Hgt1 _].
      destruct Hp2 as [Hgt2 _].
      destruct Hp3 as [Hgt3 _].
      (* Since 23 is odd, factors cannot be 2. Since 23 = p1*p2*p3, if p1=2, 2*p2*p3=23, impossible in Z. *)
      assert (p1 >= 3) by (destruct (Z.eq_dec p1 2); [subst; nia | lia]).
      assert (p2 >= 3) by (destruct (Z.eq_dec p2 2); [subst; nia | lia]).
      assert (p3 >= 3) by (destruct (Z.eq_dec p3 2); [subst; nia | lia]).
      (* p1, p2, p3 >= 3 implies p1*p2*p3 >= 27. But p1*p2*p3 = 23. Contradiction. *)
      nia.
  - (* Case: false = false <-> ... *)
    split.
    + intro H.
      right.
      intro H_exists.
      destruct H_exists as [p1 [p2 [p3 [Hp1 [Hp2 [Hp3 Heq]]]]]].
      destruct Hp1 as [Hgt1 _].
      destruct Hp2 as [Hgt2 _].
      destruct Hp3 as [Hgt3 _].
      assert (p1 >= 3) by (destruct (Z.eq_dec p1 2); [subst; nia | lia]).
      assert (p2 >= 3) by (destruct (Z.eq_dec p2 2); [subst; nia | lia]).
      assert (p3 >= 3) by (destruct (Z.eq_dec p3 2); [subst; nia | lia]).
      nia.
    + intro H. reflexivity.
Qed.