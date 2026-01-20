Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["16311/9"; "163/58"] -> x1=16311, x2=9, n1=163, n2=58
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 16311 9 163 58 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* H_res : false = true, which is a contradiction *)
    discriminate.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* H_mod : (16311 * 163) mod (9 * 58) = 0 *)
    (* Compute the values: 2658693 mod 522 = 147 *)
    vm_compute in H_mod.
    (* Now H_mod is 147 = 0, which is a contradiction *)
    discriminate.
Qed.