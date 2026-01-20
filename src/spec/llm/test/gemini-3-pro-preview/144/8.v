Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["2/3"; "5/2"] -> x1=2, x2=3, n1=5, n2=2
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 2 3 5 2 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so H_res : false = true *)
    discriminate.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* (2 * 5) mod (3 * 2) = 10 mod 6 = 4 *)
    (* H_mod implies 4 = 0 *)
    compute in H_mod.
    discriminate.
Qed.