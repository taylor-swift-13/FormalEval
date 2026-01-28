Require Import ZArith.
Require Import Bool.
Require Import Lia.

Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (result : bool) : Prop :=
  result = true <-> exists k : nat, Z.pow n (Z.of_nat k) = x.

Example test_is_simple_power : is_simple_power_spec 6 5 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - (* Left to Right: false = true -> exists k, ... *)
    intros H.
    discriminate H.
  - (* Right to Left: (exists k, ...) -> false = true *)
    intros [k Hk].
    destruct k.
    + (* k = 0 *)
      simpl in Hk.
      discriminate Hk.
    + destruct k.
      * (* k = 1 *)
        simpl in Hk.
        discriminate Hk.
      * (* k >= 2 *)
        simpl in Hk.
        (* Hk reduces to roughly 25 * 5^k = 6 *)
        assert (Hpos: 0 < 5 ^ Z.of_nat k).
        { apply Z.pow_pos_nonneg; lia. }
        (* Since 5^k > 0, 25 * 5^k >= 25, which cannot equal 6 *)
        lia.
Qed.