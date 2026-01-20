Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Lia.

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
  - intro H. lia.
  - intro H.
    split.
    + intro Htrue.
      intros d Hd1 Hd2.
      assert (d = 2 \/ d = 3 \/ d = 4) as Hcases by lia.
      destruct Hcases as [Hd | [Hd | Hd]]; subst; compute; discriminate.
    + intro Hdiv.
      reflexivity.
Qed.