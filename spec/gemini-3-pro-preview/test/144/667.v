Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["16/117"; "16/117"] -> x1=16, x2=117, n1=16, n2=117
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 16 117 16 117 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* false = true is a contradiction *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* (16 * 16) mod (117 * 117) reduces to 256 mod 13689 = 256 *)
    (* 256 = 0 is a contradiction *)
    compute in H_mod.
    discriminate H_mod.
Qed.