Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["943/29"; "45111/9984"] -> x1=943, x2=29, n1=45111, n2=9984
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 943 29 45111 9984 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* H_res : false = true, which is a contradiction *)
    inversion H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Evaluate the modulo expression to show contradiction *)
    vm_compute in H_mod.
    (* H_mod reduces to 267369 = 0 *)
    inversion H_mod.
Qed.