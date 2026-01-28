Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["176/17"; "176/17"] -> x1=176, x2=17, n1=176, n2=17
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 176 17 176 17 false.
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
    (* Calculate (176 * 176) mod (17 * 17) *)
    (* (176 * 176) = 30976 *)
    (* (17 * 17) = 289 *)
    (* 30976 mod 289 = 53 *)
    (* H_mod reduces to 53 = 0, which is false *)
    compute in H_mod.
    discriminate H_mod.
Qed.