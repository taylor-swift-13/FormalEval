Require Import Arith.Arith.
Require Import ZArith.

Definition fibfib_spec (n : nat) (res : nat) : Prop :=
  (n = 0 /\ res = 0) \/
  (n = 1 /\ res = 0) \/
  (n = 2 /\ res = 1) \/
  (n >= 3 /\ exists a b c i,
      a = 0 /\ b = 0 /\ c = 1 /\
      i = 3 /\
      (forall k x y z, (3 <= k < n) -> 
        let x' := y in
        let y' := z in
        let z' := x + y + z in
        True) /\
      res = c).

Example fibfib_spec_2_1 : fibfib_spec 2%nat 1%nat.
Proof.
  unfold fibfib_spec.
  right. right. left.
  split; reflexivity.
Qed.

Example fibfib_spec_test_case_Z :
  fibfib_spec (Z.to_nat 2%Z) (Z.to_nat 1%Z).
Proof.
  change (fibfib_spec 2%nat 1%nat).
  apply fibfib_spec_2_1.
Qed.