Require Import Arith.
Require Import ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Lia.

Open Scope Z_scope.

Definition problem_150_pre (n x y : nat) : Prop := True.

Definition problem_150_spec (n x y res : nat) : Prop :=
  (prime (Z.of_nat n) -> res = x) /\
  (~ prime (Z.of_nat n) -> res = y).

(* Lemma that 7 is prime *)
Lemma prime_7 : prime 7.
Proof.
  constructor.
  - lia.
  - intros n Hrange Hdiv.
    assert (H: Z.abs n <= 7).
    { apply Zdivide_bounds; [lia | exact Hdiv]. }
    assert (Habs: n = 1 \/ n = -1 \/ n = 7 \/ n = -7 \/
                 n = 2 \/ n = -2 \/ n = 3 \/ n = -3 \/
                 n = 4 \/ n = -4 \/ n = 5 \/ n = -5 \/
                 n = 6 \/ n = -6) by lia.
    destruct Habs as [|[|[|[|[|[|[|[|[|[|[|[|[|]]]]]]]]]]]]]; subst; try (left; reflexivity); try (right; reflexivity).
    + destruct Hdiv as [k Hk]. lia.
    + destruct Hdiv as [k Hk]. lia.
    + destruct Hdiv as [k Hk]. lia.
    + destruct Hdiv as [k Hk]. lia.
    + destruct Hdiv as [k Hk]. lia.
    + destruct Hdiv as [k Hk]. lia.
    + destruct Hdiv as [k Hk]. lia.
    + destruct Hdiv as [k Hk]. lia.
    + destruct Hdiv as [k Hk]. lia.
    + destruct Hdiv as [k Hk]. lia.
Qed.

Example problem_150_test1 : problem_150_spec 7 34 12 34.
Proof.
  unfold problem_150_spec.
  split.
  - intros _. reflexivity.
  - intros Hnp.
    exfalso.
    apply Hnp.
    simpl.
    exact prime_7.
Qed.