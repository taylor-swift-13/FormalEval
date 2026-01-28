Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["7/5725"; "8577/291"] -> x1=7, x2=5725, n1=8577, n2=291
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 7 5725 8577 291 false.
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
    (* (7 * 8577) mod (5725 * 291) *)
    (* 60039 mod 1665975 = 60039 *)
    (* 60039 = 0 is a contradiction *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.