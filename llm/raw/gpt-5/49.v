Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition modp_spec (n p res : Z) : Prop :=
0 <= n /\ 0 < p /\ res = Z.modulo (Z.pow 2 (Z.to_nat n)) p.