Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["3080/241"; "176/9"] -> x1=3080, x2=241, n1=176, n2=9
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 3080 241 176 9 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so H_res is false = true, which is a contradiction *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Calculate modulo: (3080 * 176) mod (241 * 9) *)
    (* 3080 * 176 = 542080 *)
    (* 241 * 9 = 2169 *)
    (* 542080 mod 2169 = 1999 *)
    (* H_mod implies 1999 = 0, which is a contradiction *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.