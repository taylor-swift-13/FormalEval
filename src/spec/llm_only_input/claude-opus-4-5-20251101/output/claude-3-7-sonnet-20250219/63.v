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

(* Convert Z to nat for the specification *)
Definition fibfib_spec_Z (input : Z) (output : Z) : Prop :=
  fibfib_spec (Z.to_nat input) (Z.to_nat output).

Example fibfib_test_2 : fibfib_spec_Z 2%Z 1%Z.
Proof.
  unfold fibfib_spec_Z, fibfib_spec.
  right. right. left.
  split; reflexivity.
Qed.