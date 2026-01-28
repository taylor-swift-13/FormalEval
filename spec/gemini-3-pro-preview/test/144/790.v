Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["03080/241"; "99/100"] -> x1=3080, x2=241, n1=99, n2=100
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 3080 241 99 100 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* false = true is a contradiction *)
    inversion H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Evaluate (3080 * 99) mod (241 * 100) *)
    (* 304920 mod 24100 = 15720 *)
    vm_compute in H_mod.
    (* 15720 = 0 is a contradiction *)
    discriminate.
Qed.