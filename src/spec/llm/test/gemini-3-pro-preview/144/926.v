Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["943/2"; "1683/58"] -> x1=943, x2=2, n1=1683, n2=58
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 943 2 1683 58 false.
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
    (* Calculate the modulo: (943 * 1683) mod (2 * 58) *)
    (* This evaluates to non-zero (73), so H_mod implies 73 = 0, a contradiction *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.