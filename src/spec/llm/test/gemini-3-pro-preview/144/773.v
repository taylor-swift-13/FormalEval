Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["380/241"; "8577/291"] -> x1=380, x2=241, n1=8577, n2=291
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 380 241 8577 291 false.
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
    (* Calculate (380 * 8577) mod (241 * 291) *)
    (* 3259260 mod 70131 is not 0 *)
    vm_compute in H_mod.
    (* This results in a contradiction: non-zero = 0 *)
    discriminate H_mod.
Qed.