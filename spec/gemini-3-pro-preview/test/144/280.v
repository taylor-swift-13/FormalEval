Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["8/13"; "13/77"] -> x1=8, x2=13, n1=13, n2=77
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 8 13 13 77 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    (* false = true is a contradiction *)
    intros H_res.
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Calculate (8 * 13) mod (13 * 77) *)
    (* 8 * 13 = 104 *)
    (* 13 * 77 = 1001 *)
    (* 104 mod 1001 = 104 *)
    (* H_mod implies 104 = 0, which is a contradiction *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.