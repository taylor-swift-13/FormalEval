Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  (n <= 1 -> result = false) /\
  (n > 1 -> 
    (result = true <-> 
      (forall d : Z, 2 <= d -> d < n -> Z.rem n d <> 0))).

Example test_is_prime_3 : is_prime_spec 3 true.
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
      intros _ d Hle Hlt.
      (* Since 2 <= d < 3, d must be 2 *)
      assert (d = 2) by lia.
      subst d.
      (* Verify Z.rem 3 2 <> 0 *)
      intro Hrem.
      (* Z.rem 3 2 evaluates to 1 *)
      compute in Hrem.
      discriminate Hrem.
    + (* Direction: (forall d ...) -> result = true *)
      intros _.
      reflexivity.
Qed.