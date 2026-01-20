Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["16/17"; "380/241"] -> x1=16, x2=17, n1=380, n2=241
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 16 17 380 241 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: false = true -> mod = 0 *)
    intros H_res.
    discriminate H_res.
  - (* Right to Left: mod = 0 -> false = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (16 * 380) mod (17 * 241) *)
    (* 16 * 380 = 6080 *)
    (* 17 * 241 = 4097 *)
    (* 6080 mod 4097 = 1983 *)
    compute in H_mod.
    (* H_mod is now 1983 = 0, which is a contradiction *)
    discriminate H_mod.
Qed.