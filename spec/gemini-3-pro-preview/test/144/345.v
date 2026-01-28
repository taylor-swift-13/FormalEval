Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["8577/291"; "857/291"] -> x1=8577, x2=291, n1=857, n2=291
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 8577 291 857 291 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so H_res : false = true, which is a contradiction *)
    discriminate.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Calculate (8577 * 857) mod (291 * 291) *)
    vm_compute in H_mod.
    (* H_mod reduces to 67923 = 0, which is a contradiction *)
    discriminate.
Qed.