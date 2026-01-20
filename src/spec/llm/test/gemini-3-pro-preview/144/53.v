Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["33/4"; "33/4"] -> x1=33, x2=4, n1=33, n2=4
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 33 4 33 4 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* H_res is false = true, which is a contradiction *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* (33 * 33) mod (4 * 4) reduces to 1089 mod 16, which is 1 *)
    (* H_mod becomes 1 = 0, which is a contradiction *)
    compute in H_mod.
    discriminate H_mod.
Qed.