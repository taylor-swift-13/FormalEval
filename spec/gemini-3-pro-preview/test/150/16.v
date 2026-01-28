Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.

Open Scope Z_scope.

(* Specification definition *)
Definition x_or_y_spec (n x y res : Z) : Prop :=
  (prime n -> res = x) /\
  (~ prime n -> res = y).

(* Test case: input = [113; 100; 200], output = 100 *)
Example test_x_or_y_113 : x_or_y_spec 113 100 200 100.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case: prime 113 -> 100 = 100 *)
    intros Hprime.
    reflexivity.
  - (* Case: ~ prime 113 -> 100 = 200 *)
    intros Hnot_prime.
    exfalso.
    apply Hnot_prime.
    apply prime_intro.
    + lia.
    + intros n Hrange.
      apply Zgcd_1_rel_prime.
      let rec check_all k :=
        let is_one := eval compute in (Z.eqb k 1) in
        match is_one with
        | true => lia
        | false =>
          let km1 := eval compute in (Z.pred k) in
          assert (n = km1 \/ 1 <= n < km1) as [Heq | Hlt] by lia;
          [ rewrite Heq; vm_compute; reflexivity
          | clear Hrange; rename Hlt into Hrange; check_all km1 ]
        end
      in check_all 113.
Qed.