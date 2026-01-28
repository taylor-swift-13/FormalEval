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

Example test_case_6 : is_multiply_prime_spec 6 false.
Proof.
  unfold is_multiply_prime_spec.
  split.
  - (* Case: false = true <-> ... *)
    split.
    + intro H. discriminate H.
    + intro H.
      destruct H as [_ [p1 [p2 [p3 [Hp1 [Hp2 [Hp3 Heq]]]]]]].
      unfold is_prime in *.
      destruct Hp1 as [Hgt1 _].
      destruct Hp2 as [Hgt2 _].
      destruct Hp3 as [Hgt3 _].
      (* p1, p2, p3 > 1 means p1, p2, p3 >= 2 in Z *)
      (* 2 * 2 * 2 = 8, which is > 6. Contradiction. *)
      nia.
  - (* Case: false = false <-> ... *)
    split.
    + intro H.
      (* We need to prove the RHS: 6 <= 1 \/ ~ (exists ...) *)
      right.
      intro H_exists.
      destruct H_exists as [p1 [p2 [p3 [Hp1 [Hp2 [Hp3 Heq]]]]]].
      unfold is_prime in *.
      destruct Hp1 as [Hgt1 _].
      destruct Hp2 as [Hgt2 _].
      destruct Hp3 as [Hgt3 _].
      (* Similarly, product of three integers >= 2 cannot be 6 *)
      nia.
    + intro H. reflexivity.
Qed.