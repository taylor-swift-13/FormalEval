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

Example test_case_98 : is_multiply_prime_spec 98 true.
Proof.
  unfold is_multiply_prime_spec.
  split.
  - (* result = true <-> ... *)
    split.
    + intro H.
      split.
      * lia.
      * exists 2, 7, 7.
        repeat split.
        -- (* is_prime 2 *)
           unfold is_prime. split. lia.
           intros d H_bound. lia.
        -- (* is_prime 7 *)
           unfold is_prime. split. lia.
           intros d H_bound.
           assert (d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6) as H_cases by lia.
           destruct H_cases as [? | [? | [? | [? | ?]]]]; subst; simpl; discriminate.
        -- (* is_prime 7 *)
           unfold is_prime. split. lia.
           intros d H_bound.
           assert (d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6) as H_cases by lia.
           destruct H_cases as [? | [? | [? | [? | ?]]]]; subst; simpl; discriminate.
        -- (* 98 = 2 * 7 * 7 *)
           reflexivity.
    + intro H. reflexivity.
  - (* result = false <-> ... *)
    split.
    + intro H. discriminate H.
    + intro H.
      destruct H as [H_le | H_not_exists].
      * lia.
      * exfalso. apply H_not_exists.
        exists 2, 7, 7.
        repeat split.
        -- unfold is_prime. split. lia. intros d H_bound. lia.
        -- unfold is_prime. split. lia. intros d H_bound.
           assert (d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6) as H_cases by lia.
           destruct H_cases as [? | [? | [? | [? | ?]]]]; subst; simpl; discriminate.
        -- unfold is_prime. split. lia. intros d H_bound.
           assert (d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6) as H_cases by lia.
           destruct H_cases as [? | [? | [? | [? | ?]]]]; subst; simpl; discriminate.
        -- reflexivity.
Qed.