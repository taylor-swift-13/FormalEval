Require Import Arith.
Require Import ZArith.
Require Import ZArith.Zpow_facts.
Open Scope Z_scope.

Definition problem_76_spec (x n : Z) (result : bool) : Prop :=
  result = true <-> (exists k : nat, x = n ^ (Z.of_nat k)).

Lemma problem_76_example : problem_76_spec 24 2 false.
Proof.
  unfold problem_76_spec.
  split.
  - intro H.
    destruct H as [k Hk].
    rewrite Hk in *.
    simpl in Hk.
    (* Since 2^k is always even for k > 0, and 24 = 2^3 * 3, not a pure power of 2 *)
    discriminate.
  - intro H.
    destruct H as [k Hk].
    (* But 24 cannot be written as 2^k for any k *)
    discriminate.
Qed.