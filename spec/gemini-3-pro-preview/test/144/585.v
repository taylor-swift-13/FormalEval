Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["4767/7736"; "467/776"] -> x1=4767, x2=7736, n1=467, n2=776
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 4767 7736 467 776 false.
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
    (* Evaluate the algebraic expressions *)
    (* (4767 * 467) mod (7736 * 776) *)
    (* 2226189 mod 6003136 = 2226189 *)
    (* 2226189 = 0 is false *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.