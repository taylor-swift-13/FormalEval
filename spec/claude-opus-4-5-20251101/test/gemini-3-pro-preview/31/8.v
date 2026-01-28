Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  (n <= 1 -> result = false) /\
  (n > 1 -> 
    (result = true <-> 
      (forall d : Z, 2 <= d -> d < n -> Z.rem n d <> 0))).

Example test_is_prime_5 : is_prime_spec 5 true.
Proof.
  unfold is_prime_spec.
  split.
  - (* Case: n <= 1 *)
    intros H.
    lia.
  - (* Case: n > 1 *)
    intros _.
    split.
    + (* Direction: result = true -> forall d ... *)
      intros _ d H_ge_2 H_lt_5.
      assert (H_cases: d = 2 \/ d = 3 \/ d = 4) by lia.
      destruct H_cases as [-> | [-> | ->]]; compute; discriminate.
    + (* Direction: (forall d ...) -> result = true *)
      intros _.
      reflexivity.
Qed.