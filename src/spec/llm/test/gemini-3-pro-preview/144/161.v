Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["1111/7"; "11/7"] -> x1=1111, x2=7, n1=11, n2=7
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 1111 7 11 7 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so H_res implies false = true, which is a contradiction *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* (1111 * 11) mod (7 * 7) = 12221 mod 49 = 20 *)
    (* H_mod implies 20 = 0, which is a contradiction *)
    compute in H_mod.
    discriminate H_mod.
Qed.