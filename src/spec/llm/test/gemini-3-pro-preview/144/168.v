Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["11/99"; "4453/3844"] -> x1=11, x2=99, n1=4453, n2=3844
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 11 99 4453 3844 false.
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
    (* Calculate (11 * 4453) mod (99 * 3844) *)
    (* 11 * 4453 = 48983 *)
    (* 99 * 3844 = 380556 *)
    (* 48983 mod 380556 = 48983 <> 0 *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.