Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["3080/1"; "43853/3384"] -> x1=3080, x2=1, n1=43853, n2=3384
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 3080 1 43853 3384 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so H_res : false = true, which is a contradiction *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Evaluate the modulo: (3080 * 43853) mod (1 * 3384) *)
    vm_compute in H_mod.
    (* H_mod reduces to 1648 = 0, which is a contradiction *)
    discriminate H_mod.
Qed.