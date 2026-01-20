Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["16/17"; "16/17"] -> x1=16, x2=17, n1=16, n2=17
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 16 17 16 17 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so H_res is false = true, which is impossible *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (16 * 16) mod (17 * 17) *)
    (* 256 mod 289 = 256 *)
    (* H_mod implies 256 = 0, which is impossible *)
    compute in H_mod.
    discriminate H_mod.
Qed.