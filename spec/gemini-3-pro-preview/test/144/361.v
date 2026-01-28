Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["467/77636"; "597/275"] -> x1=467, x2=77636, n1=597, n2=275
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 467 77636 597 275 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* false = true is a contradiction *)
    discriminate.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (467 * 597) mod (77636 * 275) *)
    (* 467 * 597 = 278799 *)
    (* 77636 * 275 = 21349900 *)
    (* 278799 mod 21349900 = 278799 *)
    (* 278799 = 0 is a contradiction *)
    vm_compute in H_mod.
    discriminate.
Qed.