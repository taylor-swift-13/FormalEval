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

Example test_case_25 : is_multiply_prime_spec 25 false.
Proof.
  unfold is_multiply_prime_spec.
  split.
  - (* Case: false = true <-> ... *)
    split.
    + intro H. discriminate H.
    + intro H.
      destruct H as [_ [p1 [p2 [p3 [Hp1 [Hp2 [Hp3 Heq]]]]]]].
      unfold is_prime in *.
      destruct Hp1 as [Hgt1 _], Hp2 as [Hgt2 _], Hp3 as [Hgt3 _].
      (* Logic: Primes are >= 2. 
         If any prime is 2, the product is even, but 25 is odd.
         If all primes are >= 3, the product is >= 27, but 25 < 27. *)
      assert (Hp1_cases: p1 = 2 \/ p1 >= 3) by lia.
      assert (Hp2_cases: p2 = 2 \/ p2 >= 3) by lia.
      assert (Hp3_cases: p3 = 2 \/ p3 >= 3) by lia.
      
      destruct Hp1_cases as [E1|G1]; [rewrite E1 in Heq; nia |].
      destruct Hp2_cases as [E2|G2]; [rewrite E2 in Heq; nia |].
      destruct Hp3_cases as [E3|G3]; [rewrite E3 in Heq; nia |].
      (* Case where all are >= 3 *)
      nia.
  - (* Case: false = false <-> ... *)
    split.
    + intro H.
      right.
      intro H_exists.
      destruct H_exists as [p1 [p2 [p3 [Hp1 [Hp2 [Hp3 Heq]]]]]].
      unfold is_prime in *.
      destruct Hp1 as [Hgt1 _], Hp2 as [Hgt2 _], Hp3 as [Hgt3 _].
      
      assert (Hp1_cases: p1 = 2 \/ p1 >= 3) by lia.
      assert (Hp2_cases: p2 = 2 \/ p2 >= 3) by lia.
      assert (Hp3_cases: p3 = 2 \/ p3 >= 3) by lia.
      
      destruct Hp1_cases as [E1|G1]; [rewrite E1 in Heq; nia |].
      destruct Hp2_cases as [E2|G2]; [rewrite E2 in Heq; nia |].
      destruct Hp3_cases as [E3|G3]; [rewrite E3 in Heq; nia |].
      nia.
    + intro H. reflexivity.
Qed.